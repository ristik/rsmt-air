//! BabyBear + Poseidon2 hashing for the RSMT v6a data structure.
//!
//! Keys and regions use the MSB-first 9-limb encoding of `rsmt-core::limbs`
//! (D2/D3). Two hash families:
//!
//! - **Leaf hash (D5).** Unchanged 3-step additive sponge, rate 8 / capacity 8,
//!   digest = `state[0..8]` after step 2.
//! - **Node hash (D4).** Two-permutation sponge. The **prefix block**
//!   `P2([DOMAIN_NODE, d, p[0..9], 0×5])` depends only on the junction's
//!   position `(d, p)` and is **shared** between the old-side and new-side
//!   digests of the same junction. The **children block**
//!   `P2(mid + left‖right)` folds in the child digests; digest = `out[0..8]`.

use p3_baby_bear::{
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
    BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
    BABYBEAR_POSEIDON2_RC_16_INTERNAL, BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16,
};
use p3_field::PrimeCharacteristicRing;
use p3_poseidon2_air::RoundConstants;
use p3_symmetric::Permutation;

use rsmt_core::{Hasher, Key, LIMBS, bytes_to_limbs};

/// Domain separator prepended to the leaf sponge.
pub const DOMAIN_LEAF: u32 = 1;
/// Domain separator prepended to the node prefix block.
pub const DOMAIN_NODE: u32 = 2;
pub const STATE_WIDTH: usize = 16;
pub const DIGEST_WIDTH: usize = 8;
pub const RATE: usize = 8;
pub const CAPACITY: usize = 8;

pub type Digest = [BabyBear; DIGEST_WIDTH];
pub type State = [BabyBear; STATE_WIDTH];

/// Round constants matching `default_babybear_poseidon2_16()`, in the form the
/// `p3-poseidon2-air` AIR consumes (Bus 2 lockstep in later milestones).
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

/// Convert MSB-first `[u32; 9]` limbs to BabyBear field elements. Every limb is
/// `< 2^30 < BabyBear::ORDER`, so this is injective.
#[inline]
pub fn limbs_to_field(limbs: &Key) -> [BabyBear; LIMBS] {
    core::array::from_fn(|i| BabyBear::from_u32(limbs[i]))
}

/// Pack a value (`≤ 32` bytes, right-aligned into 32) into 9 MSB-first field
/// limbs, matching the key packing.
pub fn pack_value_32(v: &[u8]) -> [BabyBear; LIMBS] {
    let mut padded = [0u8; 32];
    let n = v.len().min(32);
    padded[32 - n..].copy_from_slice(&v[..n]);
    limbs_to_field(&bytes_to_limbs(&padded))
}

/// Default deterministic Poseidon2 permutation (prover + verifier).
pub fn default_perm() -> Poseidon2BabyBear<STATE_WIDTH> {
    default_babybear_poseidon2_16()
}

// -- Node hash (two-permutation sponge, D4) ---------------------------------

/// Prefix block: `P2([DOMAIN_NODE, d, p[0..9], 0×5])`. Depends only on the
/// junction position `(d, p)`, so its output `mid` is shared between the
/// old-side and new-side children blocks of the same junction.
pub fn node_prefix_block(perm: &Poseidon2BabyBear<STATE_WIDTH>, depth: u16, region: &Key) -> State {
    let mut state = [BabyBear::ZERO; STATE_WIDTH];
    state[0] = BabyBear::from_u32(DOMAIN_NODE);
    state[1] = BabyBear::from_u32(depth as u32);
    let region_f = limbs_to_field(region);
    state[2..2 + LIMBS].copy_from_slice(&region_f);
    perm.permute_mut(&mut state);
    state
}

/// Children block: `P2(mid + left‖right)`; folds the child digests into the
/// shared `mid`. Returns the full permutation output (digest = `out[0..8]`).
pub fn node_children_block(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    mid: &State,
    left: &Digest,
    right: &Digest,
) -> State {
    let mut state = *mid;
    for i in 0..DIGEST_WIDTH {
        state[i] += left[i];
        state[DIGEST_WIDTH + i] += right[i];
    }
    perm.permute_mut(&mut state);
    state
}

/// Full node hash: prefix block then children block; digest = `out[0..8]`.
pub fn node_hash_with(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    depth: u16,
    region: &Key,
    left: &Digest,
    right: &Digest,
) -> Digest {
    let mid = node_prefix_block(perm, depth, region);
    let out = node_children_block(perm, &mid, left, right);
    let mut digest = [BabyBear::ZERO; DIGEST_WIDTH];
    digest.copy_from_slice(&out[..DIGEST_WIDTH]);
    digest
}

// -- Leaf hash (3-step additive sponge, D5) ---------------------------------

/// Three-permutation additive sponge over `(key‖value)`, 18 limbs in three
/// rate-8 chunks; first chunk's leading element is `DOMAIN_LEAF`.
pub fn leaf_hash_with(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    key: &[BabyBear; LIMBS],
    value: &[BabyBear; LIMBS],
) -> Digest {
    let mut state = [BabyBear::ZERO; STATE_WIDTH];

    // Step 0: rate = [DOMAIN_LEAF ‖ key[0..7]]
    state[0] = BabyBear::from_u32(DOMAIN_LEAF);
    state[1..RATE].copy_from_slice(&key[..RATE - 1]);
    perm.permute_mut(&mut state);

    // Step 1: rate += [key[7], key[8], value[0..6]]
    state[0] += key[7];
    state[1] += key[8];
    for i in 0..6 {
        state[2 + i] += value[i];
    }
    perm.permute_mut(&mut state);

    // Step 2: rate += [value[6], value[7], value[8]]
    state[0] += value[6];
    state[1] += value[7];
    state[2] += value[8];
    perm.permute_mut(&mut state);

    let mut digest = [BabyBear::ZERO; DIGEST_WIDTH];
    digest.copy_from_slice(&state[..DIGEST_WIDTH]);
    digest
}

// -- Permutation I/O (for the witness arena, DEVPLAN M2) --------------------

/// A single Poseidon2 evaluation as an `(input, output)` pair. The witness
/// arena stores one of these per *distinct* permutation; Table B is the arena
/// chunked 8 lanes per row, and Bus 2 carries `(input‖output)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PermIo {
    pub input: State,
    pub output: State,
}

fn eval(perm: &Poseidon2BabyBear<STATE_WIDTH>, input: State) -> PermIo {
    let mut output = input;
    perm.permute_mut(&mut output);
    PermIo { input, output }
}

/// The node prefix block as an `(input, output)` pair; `output` is `mid`.
pub fn node_prefix_io(perm: &Poseidon2BabyBear<STATE_WIDTH>, depth: u16, region: &Key) -> PermIo {
    let mut input = [BabyBear::ZERO; STATE_WIDTH];
    input[0] = BabyBear::from_u32(DOMAIN_NODE);
    input[1] = BabyBear::from_u32(depth as u32);
    input[2..2 + LIMBS].copy_from_slice(&limbs_to_field(region));
    eval(perm, input)
}

/// The node children block as an `(input, output)` pair; digest = `output[0..8]`.
pub fn node_children_io(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    mid: &State,
    left: &Digest,
    right: &Digest,
) -> PermIo {
    let mut input = *mid;
    for i in 0..DIGEST_WIDTH {
        input[i] += left[i];
        input[DIGEST_WIDTH + i] += right[i];
    }
    eval(perm, input)
}

/// The three leaf-sponge permutations as `(input, output)` pairs, in order.
/// digest = `pairs[2].output[0..8]`.
pub fn leaf_perm_io(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    key: &[BabyBear; LIMBS],
    value: &[BabyBear; LIMBS],
) -> [PermIo; 3] {
    // Step 0
    let mut input0 = [BabyBear::ZERO; STATE_WIDTH];
    input0[0] = BabyBear::from_u32(DOMAIN_LEAF);
    input0[1..RATE].copy_from_slice(&key[..RATE - 1]);
    let p0 = eval(perm, input0);

    // Step 1: rate += [key[7], key[8], value[0..6]]
    let mut input1 = p0.output;
    input1[0] += key[7];
    input1[1] += key[8];
    for i in 0..6 {
        input1[2 + i] += value[i];
    }
    let p1 = eval(perm, input1);

    // Step 2: rate += [value[6], value[7], value[8]]
    let mut input2 = p1.output;
    input2[0] += value[6];
    input2[1] += value[7];
    input2[2] += value[8];
    let p2 = eval(perm, input2);

    [p0, p1, p2]
}

/// Extract the 8-limb digest from a permutation output.
#[inline]
pub fn digest_of(state: &State) -> Digest {
    let mut d = [BabyBear::ZERO; DIGEST_WIDTH];
    d.copy_from_slice(&state[..DIGEST_WIDTH]);
    d
}

// -- Hasher impl ------------------------------------------------------------

thread_local! {
    static PERM: Poseidon2BabyBear<STATE_WIDTH> = default_perm();
}

/// Poseidon2 hasher plugging into `rsmt-core::Hasher`.
#[derive(Clone)]
pub struct Poseidon2Hasher;

impl Hasher for Poseidon2Hasher {
    type Digest = Digest;

    fn hash_leaf(key: &Key, value: &[u8]) -> Self::Digest {
        let key_f = limbs_to_field(key);
        let value_f = pack_value_32(value);
        PERM.with(|p| leaf_hash_with(p, &key_f, &value_f))
    }

    fn hash_node(depth: u16, region: &Key, lh: &Self::Digest, rh: &Self::Digest) -> Self::Digest {
        PERM.with(|p| node_hash_with(p, depth, region, lh, rh))
    }
}

#[cfg(test)]
mod tests;
