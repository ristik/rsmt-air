//! BabyBear + Poseidon2 hash spec for RSMT3.
//!
//! Provides:
//! - 256-bit ↔ 9-limb (30-bit) packing.
//! - `node_hash`: one permutation, state[0..16] = left[0..8] ‖ right[0..8],
//!   with `state[0] += DOMAIN_NODE`, `state[1] += depth`.
//! - `leaf_hash`: rate-8 / capacity-8 sponge over three permutations.

use num_bigint::BigUint;
use p3_baby_bear::{
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
    BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
    BABYBEAR_POSEIDON2_RC_16_INTERNAL, BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16,
};
use p3_field::PrimeCharacteristicRing;
use p3_poseidon2_air::RoundConstants;
use p3_symmetric::Permutation;

use rsmt_core::Hasher;
use rsmt_core::sort_key::{KEY_BYTES, key_to_bytes_be};

pub const DOMAIN_LEAF: u32 = 1;
pub const DOMAIN_NODE: u32 = 2;
pub const STATE_WIDTH: usize = 16;
pub const DIGEST_WIDTH: usize = 8;
pub const RATE: usize = 8;
pub const CAPACITY: usize = 8;
pub const LIMBS: usize = 9;
pub const LIMB_BITS: u32 = 30;

/// Round constants matching `default_babybear_poseidon2_16()` in a form the
/// `p3-poseidon2-air` AIR can consume directly. Use this in M7 (Bus 2) to
/// keep the witness Poseidon2 (rsmt-hash) and the AIR Poseidon2 in lockstep.
pub fn babybear_round_constants_16() -> RoundConstants<
    BabyBear,
    16,
    { BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS },
    { BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16 },
> {
    RoundConstants::new(
        BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
        BABYBEAR_POSEIDON2_RC_16_INTERNAL,
        BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
    )
}

pub type Digest = [BabyBear; DIGEST_WIDTH];
pub type State = [BabyBear; STATE_WIDTH];

/// Pack 256-bit big-endian bytes into 9 BabyBear elements (30-bit little-endian
/// limbs). Last limb holds the top 16 bits.
pub fn pack_256_to_9_limbs(bytes: &[u8; 32]) -> [BabyBear; LIMBS] {
    let mut bits: u128 = 0;
    let mut bit_count: u32 = 0;
    let mut byte_idx = bytes.len();
    let mut limbs = [BabyBear::ZERO; LIMBS];

    for limb in &mut limbs {
        while bit_count < LIMB_BITS && byte_idx > 0 {
            byte_idx -= 1;
            bits |= (bytes[byte_idx] as u128) << bit_count;
            bit_count += 8;
        }
        let v = (bits & ((1u128 << LIMB_BITS) - 1)) as u32;
        bits >>= LIMB_BITS;
        bit_count = bit_count.saturating_sub(LIMB_BITS);
        *limb = BabyBear::from_u32(v);
    }
    limbs
}

pub fn pack_biguint(k: &BigUint) -> [BabyBear; LIMBS] {
    pack_256_to_9_limbs(&key_to_bytes_be(k))
}

/// Pack a 32-byte value (e.g. CertDataHash) into 9 limbs the same way.
pub fn pack_value_32(v: &[u8]) -> [BabyBear; LIMBS] {
    let mut padded = [0u8; 32];
    let n = v.len().min(KEY_BYTES);
    padded[KEY_BYTES - n..].copy_from_slice(&v[..n]);
    pack_256_to_9_limbs(&padded)
}

/// One permutation per node hash.
pub fn node_hash_input(left: &Digest, right: &Digest, depth: u8) -> State {
    let mut state = [BabyBear::ZERO; STATE_WIDTH];
    state[..DIGEST_WIDTH].copy_from_slice(left);
    state[DIGEST_WIDTH..].copy_from_slice(right);
    state[0] += BabyBear::from_u32(DOMAIN_NODE);
    state[1] += BabyBear::from_u32(depth as u32);
    state
}

pub fn node_hash_full_with(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    left: &Digest,
    right: &Digest,
    depth: u8,
) -> State {
    let mut state = node_hash_input(left, right, depth);
    perm.permute_mut(&mut state);
    state
}

pub fn node_hash_with(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    left: &Digest,
    right: &Digest,
    depth: u8,
) -> Digest {
    let state = node_hash_full_with(perm, left, right, depth);
    let mut out = [BabyBear::ZERO; DIGEST_WIDTH];
    out.copy_from_slice(&state[..DIGEST_WIDTH]);
    out
}

pub fn node_hash_full(left: &Digest, right: &Digest, depth: u8) -> State {
    PERM.with(|p| node_hash_full_with(p, left, right, depth))
}

/// Three-permutation sponge over (key‖value), 18 limbs absorbed in three
/// rate-8 chunks. First chunk's leading element is `DOMAIN_LEAF`.
pub fn leaf_hash_with(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    key_limbs: &[BabyBear; LIMBS],
    value_limbs: &[BabyBear; LIMBS],
) -> Digest {
    let mut state = [BabyBear::ZERO; STATE_WIDTH];

    // Absorb 1: rate = [DOMAIN_LEAF ‖ key[0..7]]
    state[0] = BabyBear::from_u32(DOMAIN_LEAF);
    state[1..RATE].copy_from_slice(&key_limbs[..RATE - 1]);
    perm.permute_mut(&mut state);

    // Absorb 2: rate = [key[7..9] ‖ value[0..6]]
    state[0] += key_limbs[7];
    state[1] += key_limbs[8];
    for i in 0..6 {
        state[2 + i] += value_limbs[i];
    }
    perm.permute_mut(&mut state);

    // Absorb 3: rate = [value[6..9] ‖ pad(0,0,0,0,0)]
    state[0] += value_limbs[6];
    state[1] += value_limbs[7];
    state[2] += value_limbs[8];
    perm.permute_mut(&mut state);

    let mut out = [BabyBear::ZERO; DIGEST_WIDTH];
    out.copy_from_slice(&state[..DIGEST_WIDTH]);
    out
}

/// Default (deterministic) Poseidon2 permutation used by both prover and
/// verifier.
pub fn default_perm() -> Poseidon2BabyBear<STATE_WIDTH> {
    default_babybear_poseidon2_16()
}

/// `Hasher` impl plugging Poseidon2 into the SMT.
#[derive(Clone)]
pub struct Poseidon2Hasher;

thread_local! {
    static PERM: Poseidon2BabyBear<STATE_WIDTH> = default_perm();
}

impl Hasher for Poseidon2Hasher {
    type Digest = Digest;

    fn hash_leaf(key: &BigUint, value: &[u8]) -> Self::Digest {
        let key_bytes = key_to_bytes_be(key);
        let key_limbs = pack_256_to_9_limbs(&key_bytes);
        let value_limbs = pack_value_32(value);
        PERM.with(|p| leaf_hash_with(p, &key_limbs, &value_limbs))
    }

    fn hash_node(lh: &Self::Digest, rh: &Self::Digest, depth: u8) -> Self::Digest {
        PERM.with(|p| node_hash_with(p, lh, rh, depth))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_roundtrip_zero() {
        let limbs = pack_256_to_9_limbs(&[0u8; 32]);
        for l in &limbs {
            assert_eq!(*l, BabyBear::ZERO);
        }
    }

    #[test]
    fn pack_low_byte() {
        // Big-endian byte 31 = 0xAB → low limb = 0xAB
        let mut bytes = [0u8; 32];
        bytes[31] = 0xAB;
        let limbs = pack_256_to_9_limbs(&bytes);
        assert_eq!(limbs[0], BabyBear::from_u32(0xAB));
        for l in &limbs[1..] {
            assert_eq!(*l, BabyBear::ZERO);
        }
    }

    #[test]
    fn node_hash_deterministic() {
        let perm = default_perm();
        let l = [BabyBear::from_u32(1); DIGEST_WIDTH];
        let r = [BabyBear::from_u32(2); DIGEST_WIDTH];
        let a = node_hash_with(&perm, &l, &r, 7);
        let b = node_hash_with(&perm, &l, &r, 7);
        let c = node_hash_with(&perm, &l, &r, 8);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn leaf_hash_changes_with_value() {
        let perm = default_perm();
        let k = pack_biguint(&BigUint::from(42u32));
        let v1 = pack_value_32(&[0u8; 32]);
        let mut v2_bytes = [0u8; 32];
        v2_bytes[31] = 1;
        let v2 = pack_256_to_9_limbs(&v2_bytes);
        assert_ne!(
            leaf_hash_with(&perm, &k, &v1),
            leaf_hash_with(&perm, &k, &v2)
        );
    }

    #[test]
    fn poseidon2_hasher_smt_roundtrip() {
        use rsmt_core::{Tree, verify_consistency};
        let mut tree: Tree<Poseidon2Hasher> = Tree::new();
        let batch: Vec<_> = (0u32..16)
            .map(|i| (BigUint::from(i * 7919 + 1), vec![i as u8; 32]))
            .collect();
        let pre = tree.root_hash();
        let (items, proof) = tree.batch_insert(batch);
        let post = tree.root_hash().unwrap();
        verify_consistency::<Poseidon2Hasher>(&proof, pre.as_ref(), &post, &items).expect("verify");
    }
}
