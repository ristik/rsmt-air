//! Poseidon2 hashing tests: determinism, per-field sensitivity, prefix-block
//! sharing, and structural parity with the SHA-256 reference hasher (M0).

use p3_field::PrimeCharacteristicRing;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, Op, Sha256RefHasher, Tree, Value32, bytes_to_limbs, region_limbs};

use super::*;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

fn rand_digest(rng: &mut Xoshiro256PlusPlus) -> Digest {
    core::array::from_fn(|_| BabyBear::from_u32(rng.random::<u32>() % (1 << 30)))
}

#[test]
fn node_hash_deterministic() {
    let perm = default_perm();
    let region = region_limbs(&bytes_to_limbs(&[0xAB; 32]), 7);
    let l = [BabyBear::from_u32(1); DIGEST_WIDTH];
    let r = [BabyBear::from_u32(2); DIGEST_WIDTH];
    let a = node_hash_with(&perm, 7, &region, &l, &r);
    let b = node_hash_with(&perm, 7, &region, &l, &r);
    assert_eq!(a, b);
}

#[test]
fn node_hash_changes_on_depth() {
    let perm = default_perm();
    let region = region_limbs(&bytes_to_limbs(&[0xAB; 32]), 7);
    let l = [BabyBear::from_u32(1); DIGEST_WIDTH];
    let r = [BabyBear::from_u32(2); DIGEST_WIDTH];
    // region canonical for both depths so only depth differs in the preimage
    let r6 = region_limbs(&region, 6);
    let r7 = region_limbs(&region, 7);
    assert_ne!(
        node_hash_with(&perm, 6, &r6, &l, &r),
        node_hash_with(&perm, 7, &r7, &l, &r)
    );
}

#[test]
fn node_hash_changes_on_each_region_limb() {
    let perm = default_perm();
    let base = [BabyBear::from_u32(3); DIGEST_WIDTH];
    let region0 = [0u32; 9];
    let d = node_hash_with(&perm, 200, &region0, &base, &base);
    for j in 0..9 {
        let mut region = region0;
        region[j] = 1; // flip one limb
        assert_ne!(
            node_hash_with(&perm, 200, &region, &base, &base),
            d,
            "region limb {j} did not affect digest"
        );
    }
}

#[test]
fn node_hash_changes_on_each_child_limb() {
    let perm = default_perm();
    let region = [0u32; 9];
    let l = [BabyBear::ZERO; DIGEST_WIDTH];
    let r = [BabyBear::ZERO; DIGEST_WIDTH];
    let d = node_hash_with(&perm, 12, &region, &l, &r);
    for j in 0..DIGEST_WIDTH {
        let mut lx = l;
        lx[j] = BabyBear::ONE;
        assert_ne!(
            node_hash_with(&perm, 12, &region, &lx, &r),
            d,
            "left limb {j}"
        );
        let mut rx = r;
        rx[j] = BabyBear::ONE;
        assert_ne!(
            node_hash_with(&perm, 12, &region, &l, &rx),
            d,
            "right limb {j}"
        );
    }
}

#[test]
fn prefix_block_is_shared() {
    // The prefix block depends only on (depth, region); the old-side and
    // new-side digests of one junction reuse the same `mid`.
    let perm = default_perm();
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(1);
    let region = region_limbs(&rand_key(&mut rng), 42);
    let mid = node_prefix_block(&perm, 42, &region);

    let (l_old, r_old) = (rand_digest(&mut rng), rand_digest(&mut rng));
    let (l_new, r_new) = (rand_digest(&mut rng), rand_digest(&mut rng));

    // digests via the shared mid
    let old_shared = node_children_block(&perm, &mid, &l_old, &r_old);
    let new_shared = node_children_block(&perm, &mid, &l_new, &r_new);
    // digests via the full path (recomputing the prefix each time)
    let old_full = node_hash_with(&perm, 42, &region, &l_old, &r_old);
    let new_full = node_hash_with(&perm, 42, &region, &l_new, &r_new);

    assert_eq!(&old_shared[..DIGEST_WIDTH], &old_full[..]);
    assert_eq!(&new_shared[..DIGEST_WIDTH], &new_full[..]);
}

#[test]
fn perm_io_reproduces_digests() {
    // The arena I/O helpers must reproduce exactly the same digests as the
    // high-level hash functions, and chain correctly (output_i == input_{i+1}
    // before the additive injection).
    let perm = default_perm();
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(7);

    // node
    let region = region_limbs(&rand_key(&mut rng), 100);
    let (l, r) = (rand_digest(&mut rng), rand_digest(&mut rng));
    let pre = node_prefix_io(&perm, 100, &region);
    assert_eq!(pre.output, node_prefix_block(&perm, 100, &region));
    let ch = node_children_io(&perm, &pre.output, &l, &r);
    assert_eq!(
        digest_of(&ch.output),
        node_hash_with(&perm, 100, &region, &l, &r)
    );

    // leaf
    let key = limbs_to_field(&rand_key(&mut rng));
    let value = value_field_limbs(&Value32::new([9u8; 32]));
    let pairs = leaf_perm_io(&perm, &key, &value);
    assert_eq!(
        digest_of(&pairs[2].output),
        leaf_hash_with(&perm, &key, &value)
    );
    // each permutation's output is genuinely P2(input)
    for io in &pairs {
        let mut check = io.input;
        perm.permute_mut(&mut check);
        assert_eq!(check, io.output);
    }
}

#[test]
fn leaf_hash_changes_with_key_and_value() {
    let perm = default_perm();
    let k1 = limbs_to_field(&bytes_to_limbs(&[1; 32]));
    let k2 = limbs_to_field(&bytes_to_limbs(&[2; 32]));
    let v1 = value_field_limbs(&Value32::new([0; 32]));
    let mut vb = [0u8; 32];
    vb[31] = 1;
    let v2 = value_field_limbs(&Value32::new(vb));
    assert_ne!(
        leaf_hash_with(&perm, &k1, &v1),
        leaf_hash_with(&perm, &k2, &v1)
    );
    assert_ne!(
        leaf_hash_with(&perm, &k1, &v1),
        leaf_hash_with(&perm, &k1, &v2)
    );
}

/// Project an op to its hasher-independent structure (kind + depth + key/region
/// limbs), dropping all digest fields.
#[derive(PartialEq, Debug)]
enum Shape {
    S,
    O { depth: u16, region: Key },
    Ol { key: Key },
    L,
    N { depth: u16 },
}

fn shape<D>(op: &Op<D>) -> Shape {
    match op {
        Op::S(_) => Shape::S,
        Op::O { depth, region, .. } => Shape::O {
            depth: *depth,
            region: *region,
        },
        Op::OL { key, .. } => Shape::Ol { key: *key },
        Op::L => Shape::L,
        Op::N { depth } => Shape::N { depth: *depth },
    }
}

#[test]
fn structure_matches_reference_hasher_digests_differ() {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(2024);
    let mut t_p: Tree<Poseidon2Hasher> = Tree::new();
    let mut t_s: Tree<Sha256RefHasher> = Tree::new();
    let mut old_p = t_p.root_hash();

    for _round in 0..6 {
        let n = 1 + (rng.random::<u32>() % 40) as usize;
        let batch_p: Vec<(Key, Value32)> = (0..n)
            .map(|_| {
                (rand_key(&mut rng), {
                    let mut b = [0u8; 32];
                    rng.fill(b.as_mut_slice());
                    Value32::new(b)
                })
            })
            .collect();
        let batch_s = batch_p.clone();

        let (ap, pp) = t_p.batch_insert(batch_p);
        let (as_, ps) = t_s.batch_insert(batch_s);

        // same applied set, same opcode structure (digests deliberately differ)
        assert_eq!(ap, as_);
        let shp: Vec<Shape> = pp.iter().map(shape).collect();
        let shs: Vec<Shape> = ps.iter().map(shape).collect();
        assert_eq!(shp, shs, "opcode structure diverged between hashers");

        let new_p = t_p.root_hash();
        if !ap.is_empty() {
            let nr = new_p.unwrap();
            rsmt_core::verify_consistency::<Poseidon2Hasher>(&pp, old_p.as_ref(), &nr, &ap)
                .expect("poseidon2 verify");
        }
        old_p = new_p;
    }
}

/// R3/M1 differential property test tying together the three representations:
/// external 32-byte `Value32`/`Key32`, the internal MSB-first limbs, and the
/// Poseidon2 leaf hash. Confirms the high-level `Hasher::hash_leaf` (which packs
/// bytes→limbs internally) agrees with the low-level `leaf_hash_with` on
/// independently packed limbs, and that byte↔limb is a round trip.
#[test]
fn byte_limb_poseidon_leaf_differential() {
    use rsmt_core::{Hasher, Key32, limbs_to_bytes};
    let perm = default_perm();
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0xD1FF);
    for _ in 0..2000 {
        let mut kb = [0u8; 32];
        let mut vb = [0u8; 32];
        rng.fill(kb.as_mut_slice());
        rng.fill(vb.as_mut_slice());
        let key = Key32::new(kb);
        let value = Value32::new(vb);

        // byte→limb→byte round trip (both key and value pack identically).
        assert_eq!(limbs_to_bytes(&key.limbs()), kb);
        assert_eq!(limbs_to_bytes(&value.limbs()), vb);

        // limb-level hash == byte-level Hasher::hash_leaf.
        let low = leaf_hash_with(
            &perm,
            &limbs_to_field(&key.limbs()),
            &value_field_limbs(&value),
        );
        let high = <Poseidon2Hasher as Hasher>::hash_leaf(&key.limbs(), &value);
        assert_eq!(low, high, "limb-path and byte-path leaf hashes diverge");
    }
}
