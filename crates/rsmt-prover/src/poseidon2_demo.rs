//! End-to-end FRI proof of a `VectorizedPoseidon2Air` over BabyBear.
//!
//! This is M4 from the implementation plan: it shows that the prover
//! pipeline (`StarkConfig` + `TwoAdicFriPcs` + Poseidon2 MMCS + duplex
//! challenger + `prove` / `verify`) is functional. Tables A/F/C/D/E will
//! plug into the same pipeline via `p3-batch-stark`.

use p3_baby_bear::{
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
    BABYBEAR_S_BOX_DEGREE, BabyBear, GenericPoseidon2LinearLayersBabyBear, Poseidon2BabyBear,
};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_poseidon2_air::{RoundConstants, VectorizedPoseidon2Air};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkConfig, prove, verify};
use rand::SeedableRng;
use rand::rngs::SmallRng;

pub const P2_WIDTH: usize = 16;
pub const P2_LOG_VECTOR_LEN: u8 = 3;
pub const P2_VECTOR_LEN: usize = 1 << P2_LOG_VECTOR_LEN;
pub const SBOX_DEGREE: u64 = BABYBEAR_S_BOX_DEGREE;
pub const SBOX_REGISTERS: usize = 1;
pub const PARTIAL_ROUNDS: usize = BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16;
pub const HALF_FULL_ROUNDS: usize = BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS;

type F = BabyBear;
type EF = BinomialExtensionField<F, 4>;
type Perm16 = Poseidon2BabyBear<16>;
type Perm24 = Poseidon2BabyBear<24>;
type Sponge = PaddingFreeSponge<Perm24, 24, 16, 8>;
type Compress = TruncatedPermutation<Perm16, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<
    <F as p3_field::Field>::Packing,
    <F as p3_field::Field>::Packing,
    Sponge,
    Compress,
    2,
    8,
>;
type ChallengeMmcs = ExtensionMmcs<F, EF, ValMmcs>;
type Dft = Radix2DitParallel<F>;
type Pcs = TwoAdicFriPcs<F, Dft, ValMmcs, ChallengeMmcs>;
type Challenger = DuplexChallenger<F, Perm24, 24, 16>;
type Config = StarkConfig<Pcs, EF, Challenger>;

pub type RsmtPoseidon2Air = VectorizedPoseidon2Air<
    F,
    GenericPoseidon2LinearLayersBabyBear,
    P2_WIDTH,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS,
    P2_VECTOR_LEN,
>;

/// Prove and verify `num_hashes` Poseidon2 permutations.
pub fn prove_and_verify_poseidon2(num_hashes: usize) {
    assert!(num_hashes.is_multiple_of(P2_VECTOR_LEN));
    assert!((num_hashes / P2_VECTOR_LEN).is_power_of_two());

    let mut rng = SmallRng::seed_from_u64(1);
    let constants = RoundConstants::from_rng(&mut rng);
    let air: RsmtPoseidon2Air = VectorizedPoseidon2Air::new(constants);

    let perm16 = Perm16::new_from_rng_128(&mut rng);
    let perm24 = Perm24::new_from_rng_128(&mut rng);
    let sponge = Sponge::new(perm24.clone());
    let compress = Compress::new(perm16);
    let val_mmcs = ValMmcs::new(sponge, compress, 3);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters::new_benchmark_high_arity(challenge_mmcs);

    let trace = air.generate_vectorized_trace_rows(num_hashes, fri_params.log_blowup);

    let dft = Dft::default();
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm24);
    let config = Config::new(pcs, challenger);

    let proof = prove(&config, &air, trace, &[]);
    verify(&config, &air, &proof, &[]).expect("verify");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poseidon2_64_perms_proves_and_verifies() {
        // 64 perms = 8 rows of 8 vectorized perms each — smallest pow-of-2 trace.
        prove_and_verify_poseidon2(64);
    }
}
