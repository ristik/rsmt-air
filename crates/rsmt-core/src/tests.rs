#![allow(clippy::clone_on_copy, clippy::type_complexity)]
//! Reference-core tests: honest histories, the shadow-insertion attack, tamper
//! rejection, certificates, and a cross-language golden root. Ported from the
//! `rsmt6a.py` self-tests.

use num_bigint::BigUint;
use proptest::prelude::*;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use crate::*;

type H = Sha256RefHasher;
type D = <H as Hasher>::Digest;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut bytes = [0u8; 32];
    rng.fill(&mut bytes);
    bytes_to_limbs(&bytes)
}

fn rand_value(rng: &mut Xoshiro256PlusPlus) -> Vec<u8> {
    let mut v = vec![0u8; 8];
    rng.fill(v.as_mut_slice());
    v
}

/// Drive `rounds` random batches through a fresh tree, verifying each round's
/// consistency proof. Returns the accumulated (key, value) map and final root.
fn honest_history(
    seed: u64,
    rounds: usize,
    sizes: &[usize],
) -> (std::collections::BTreeMap<Key, Vec<u8>>, Option<D>) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<H> = Tree::new();
    let mut recorded = std::collections::BTreeMap::new();
    let mut root = tree.root_hash();
    for r in 0..rounds {
        let n = sizes[r % sizes.len()];
        let batch: Vec<(Key, Vec<u8>)> = (0..n)
            .map(|_| (rand_key(&mut rng), rand_value(&mut rng)))
            .collect();
        let (applied, proof) = tree.batch_insert(batch);
        let new_root = tree.root_hash();
        if applied.is_empty() {
            // Empty applied set: identity transition (caller's job, D6).
            assert!(proof.is_empty());
            assert_eq!(root, new_root);
            continue;
        }
        let nr = new_root.clone().unwrap();
        verify_consistency::<H>(&proof, root.as_ref(), &nr, &applied)
            .unwrap_or_else(|e| panic!("round {r} verify: {e:?}"));
        for (k, v) in applied {
            recorded.insert(k, v);
        }
        root = new_root;
    }
    (recorded, root)
}

#[test]
fn genesis_is_empty() {
    let tree: Tree<H> = Tree::new();
    assert_eq!(tree.root_hash(), None);
}

#[test]
fn empty_batch_is_identity() {
    let mut tree: Tree<H> = Tree::new();
    let (items, proof) = tree.batch_insert(vec![]);
    assert!(items.is_empty() && proof.is_empty());
    // verify accepts empty proof only when old == new.
    // (genesis: old = new = None is not representable at the boundary here;
    //  test the non-empty-tree identity instead.)
    let k = key_from_u128(0x1234);
    tree.batch_insert(vec![(k, vec![1])]);
    let root = tree.root_hash().unwrap();
    let (items, proof) = tree.batch_insert(vec![(k, vec![2])]); // already present
    assert!(items.is_empty() && proof.is_empty());
    assert!(verify_consistency::<H>(&proof, Some(&root), &root, &items).is_ok());
    // Non-empty proof with empty batch is rejected.
    assert_eq!(
        verify_consistency::<H>(&[Op::S(root)], Some(&root), &root, &[]),
        Err(VerifyError::EmptyBatchMismatch)
    );
}

#[test]
fn single_leaf_roundtrip() {
    let mut tree: Tree<H> = Tree::new();
    let k = key_from_u128(0x1234);
    let pre = tree.root_hash();
    let (items, proof) = tree.batch_insert(vec![(k, vec![0xAA; 4])]);
    let post = tree.root_hash().unwrap();
    assert_eq!(proof, vec![Op::L]); // single new leaf, no junction
    verify_consistency::<H>(&proof, pre.as_ref(), &post, &items).unwrap();
}

#[test]
fn valid_multi_round_history() {
    let (recorded, root) = honest_history(6, 8, &[1, 3, 17, 200]);
    assert!(root.is_some());
    assert!(!recorded.is_empty());
}

#[test]
fn certificates_verify() {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(11);
    let mut tree: Tree<H> = Tree::new();
    let mut recorded: Vec<(Key, Vec<u8>)> = Vec::new();
    for _ in 0..4 {
        let batch: Vec<(Key, Vec<u8>)> = (0..40)
            .map(|_| (rand_key(&mut rng), rand_value(&mut rng)))
            .collect();
        let (applied, _) = tree.batch_insert(batch);
        recorded.extend(applied);
    }
    let root = tree.root_hash().unwrap();
    for (k, v) in &recorded {
        let cert = tree.inclusion_cert(k).expect("present key has cert");
        assert!(verify_inclusion::<H>(&cert, &root, k, v));
        // wrong value fails
        assert!(!verify_inclusion::<H>(&cert, &root, k, b"wrong"));
    }
    // Absent keys: non-inclusion witnesses verify.
    let mut checked = 0;
    for _ in 0..200 {
        let k = rand_key(&mut rng);
        if recorded.iter().any(|(rk, _)| *rk == k) {
            continue;
        }
        assert!(tree.inclusion_cert(&k).is_none());
        let w = tree.non_inclusion_witness(&k).expect("absent key witness");
        assert!(verify_non_inclusion::<H>(&w, Some(&root), &k));
        checked += 1;
    }
    assert!(checked > 50);
}

/// Build a multi-key tree and return (tree, root, a recorded key).
fn tree_with_keys(seed: u64, n: usize) -> (Tree<H>, D, Vec<(Key, Vec<u8>)>) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<H> = Tree::new();
    let batch: Vec<(Key, Vec<u8>)> = (0..n)
        .map(|_| (rand_key(&mut rng), rand_value(&mut rng)))
        .collect();
    let (applied, _) = tree.batch_insert(batch);
    let root = tree.root_hash().unwrap();
    (tree, root, applied)
}

#[test]
fn shadow_insertion_attack_rejected() {
    let (tree, root, applied) = tree_with_keys(6, 64);
    let k = applied[0].0;
    let v_prime = b"equivocation".to_vec();
    // first bit position where k has a 1 bit
    let d_star = (0..KEY_BITS).find(|&d| key_bit(&k, d) == 1).unwrap();

    // fake new root: hang the whole old tree on side 0, new leaf on side 1
    let leaf_kv = H::hash_leaf(&k, &v_prime);
    let region = region_limbs(&k, d_star);
    let fake_root = H::hash_node(d_star, &region, &root, &leaf_kv);

    // (a) opaque S under the new junction: no advice → confinement rejects.
    let attack_a = vec![Op::S(root), Op::L, Op::N { depth: d_star }];
    assert_eq!(
        verify_consistency::<H>(&attack_a, Some(&root), &fake_root, &[(k, v_prime.clone())]),
        Err(VerifyError::ConfinementViolation)
    );

    // (b) opened O under the new junction: edge coherence fails.
    let root_node = match tree.root.as_deref().unwrap() {
        Node::Junction {
            depth,
            region,
            left,
            right,
            ..
        } => (*depth, *region, left.hash().clone(), right.hash().clone()),
        _ => panic!("expected junction root"),
    };
    let attack_b = vec![
        Op::O {
            depth: root_node.0,
            region: root_node.1,
            c_l: root_node.2,
            c_r: root_node.3,
        },
        Op::L,
        Op::N { depth: d_star },
    ];
    assert!(verify_consistency::<H>(&attack_b, Some(&root), &fake_root, &[(k, v_prime)]).is_err());
}

#[test]
fn re_recording_present_key_rejected() {
    let (mut tree, root, applied) = tree_with_keys(7, 40);
    let k = applied[0].0;
    let v_prime = b"equivocation".to_vec();

    // honest path: dedup skips it
    let (a, p) = tree.batch_insert(vec![(k, v_prime.clone())]);
    assert!(a.is_empty() && p.is_empty());

    // adversarial path: every crafted placement is rejected somewhere.
    for d_try in 0..12u16 {
        let p_try = region_limbs(&k, d_try);
        let forged = H::hash_node(d_try, &p_try, &H::hash_leaf(&k, &v_prime), &root);
        let stream = vec![Op::L, Op::S(root), Op::N { depth: d_try }];
        assert!(
            verify_consistency::<H>(&stream, Some(&root), &forged, &[(k, v_prime.clone())])
                .is_err(),
            "d_try={d_try}"
        );
    }
}

#[test]
fn tamper_checks_rejected() {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(99);
    let mut tree: Tree<H> = Tree::new();
    let (_a1, _p1) = tree.batch_insert(
        (0..64)
            .map(|_| (rand_key(&mut rng), b"a".to_vec()))
            .collect(),
    );
    let r1 = tree.root_hash().unwrap();
    let (a2, p2) = tree.batch_insert(
        (0..64)
            .map(|_| (rand_key(&mut rng), b"b".to_vec()))
            .collect(),
    );
    let r2 = tree.root_hash().unwrap();

    // honest
    verify_consistency::<H>(&p2, Some(&r1), &r2, &a2).unwrap();

    // dropped batch item
    assert!(verify_consistency::<H>(&p2, Some(&r1), &r2, &a2[..a2.len() - 1]).is_err());

    // duplicate batch key
    let mut dup = a2.clone();
    dup.push(a2[0].clone());
    assert_eq!(
        verify_consistency::<H>(&p2, Some(&r1), &r2, &dup),
        Err(VerifyError::BatchNotSorted)
    );

    // shift a junction depth
    let mut bad = p2.clone();
    for op in bad.iter_mut() {
        if let Op::N { depth } = op {
            *depth = (*depth + 1) % KEY_BITS;
            break;
        }
    }
    assert!(verify_consistency::<H>(&bad, Some(&r1), &r2, &a2).is_err());

    // flip an authenticated opening region bit
    let mut bad = p2.clone();
    let mut changed = false;
    for op in bad.iter_mut() {
        if let Op::O { region, .. } = op {
            region[8] ^= 1;
            changed = true;
            break;
        }
    }
    if changed {
        assert!(verify_consistency::<H>(&bad, Some(&r1), &r2, &a2).is_err());
    }

    // change values
    let changed_vals: Vec<(Key, Vec<u8>)> = a2.iter().map(|(k, _)| (*k, b"x".to_vec())).collect();
    assert!(verify_consistency::<H>(&p2, Some(&r1), &r2, &changed_vals).is_err());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Random multi-round histories always verify.
    #[test]
    fn prop_histories_verify(seed in any::<u64>()) {
        let (recorded, root) = honest_history(seed, 5, &[1, 2, 9, 33]);
        prop_assert!(root.is_some() || recorded.is_empty());
    }

    /// A single mutation of the opcode stream is rejected.
    #[test]
    fn prop_mutation_rejected(seed in any::<u64>(), which in 0usize..64) {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
        let mut tree: Tree<H> = Tree::new();
        let batch: Vec<(Key, Vec<u8>)> =
            (0..16).map(|_| (rand_key(&mut rng), rand_value(&mut rng))).collect();
        let (applied, proof) = tree.batch_insert(batch);
        prop_assume!(!applied.is_empty());
        let root = tree.root_hash().unwrap();
        verify_consistency::<H>(&proof, None, &root, &applied).unwrap();

        // Mutate one N depth in the stream (if any).
        let n_positions: Vec<usize> = proof.iter().enumerate()
            .filter(|(_, o)| matches!(o, Op::N { .. }))
            .map(|(i, _)| i).collect();
        prop_assume!(!n_positions.is_empty());
        let pos = n_positions[which % n_positions.len()];
        let mut bad = proof.clone();
        if let Op::N { depth } = &mut bad[pos] {
            *depth = (*depth + 1) % KEY_BITS;
        }
        prop_assert!(verify_consistency::<H>(&bad, None, &root, &applied).is_err());
    }
}

// ---------------------------------------------------------------------------
// Cross-language golden root (D10). Values are byte-identical to a Python run
// of rsmt6a.py over the same batch; see `GOLDEN` derivation in the test.
// ---------------------------------------------------------------------------

#[test]
fn golden_root_and_stream_match_python() {
    // Batch: keys 1,2,3,...,8 (as 256-bit ints), values b"v0".. b"v7".
    // Golden values produced by `rsmt6a.py::batch_insert` on the same input.
    let batch: Vec<(Key, Vec<u8>)> = (0u128..8)
        .map(|i| (key_from_u128(i + 1), format!("v{i}").into_bytes()))
        .collect();
    let mut tree: Tree<H> = Tree::new();
    let (applied, proof) = tree.batch_insert(batch);
    let root = tree.root_hash().unwrap();

    assert_eq!(hex(&root), GOLDEN_ROOT, "root diverged from rsmt6a.py");

    // Exact opcode stream (genesis: all L, junctions at the divergence depths).
    let golden_stream = [
        None,
        None,
        None,
        Some(255u16),
        Some(254),
        None,
        None,
        Some(255),
        None,
        None,
        Some(255),
        Some(254),
        Some(253),
        None,
        Some(252),
    ];
    let got_stream: Vec<Option<u16>> = proof
        .iter()
        .map(|op| match op {
            Op::L => None,
            Op::N { depth } => Some(*depth),
            other => panic!("unexpected op in genesis stream: {other:?}"),
        })
        .collect();
    assert_eq!(
        got_stream, golden_stream,
        "opcode stream diverged from rsmt6a.py"
    );

    // The stream verifies against the golden root.
    verify_consistency::<H>(&proof, None, &root, &applied).unwrap();

    // sanity: BigUint round-trips through the limb encoding
    let k = key_from_biguint(&BigUint::from(0x0123_4567_89ABu64));
    assert_eq!(key_to_biguint(&k), BigUint::from(0x0123_4567_89ABu64));
}

fn hex(d: &[u8; 32]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

const GOLDEN_ROOT: &str = "eea9dea8c27877e62cb5ef68b4f78cad0d6e46d4f5978c4f6b3d8d4d9bed22c9";
