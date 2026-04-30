//! End-to-end FRI proof of Table A's local constraints (no LogUp yet).
//!
//! Builds a real consistency proof, lowers it to a Table A trace, and runs
//! `p3_uni_stark::{prove, verify}` over it. Confirms that the constraint
//! system is FRI-provable in isolation before bus integration.

use num_bigint::BigUint;
use p3_baby_bear::{
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
    BABYBEAR_S_BOX_DEGREE,
};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    StarkConfig, prove_with_preprocessed, setup_preprocessed, verify_with_preprocessed,
};
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_air::{TableAAir, table_a};
use rsmt_core::{Tree, get_sort_key};
use rsmt_hash::{DIGEST_WIDTH, Poseidon2Hasher};
use rsmt_witness::build_table_a;

const _: () = {
    let _ = BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS;
    let _ = BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16;
    let _ = BABYBEAR_S_BOX_DEGREE;
};

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

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
    let mut bytes = [0u8; 32];
    rng.fill(&mut bytes);
    BigUint::from_bytes_be(&bytes)
}

/// Build a random batch, run the verifier, lower to Table A, then
/// `prove`/`verify` via FRI.
pub fn prove_and_verify_table_a(seed: u64, batch_size: usize) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();

    let batch: Vec<_> = (0..batch_size)
        .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
        .collect();
    let pre_root = tree.root_hash();
    let (items, proof) = tree.batch_insert(batch);
    let post_root = tree.root_hash().expect("post root");
    let mut sorted = items;
    sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

    let rows = build_table_a::<Poseidon2Hasher>(&proof, &sorted);
    let (trace, real, height) = table_a::build_trace_babybear(&rows);
    let air = TableAAir::new(height, real);

    let mut publics = Vec::with_capacity(2 * DIGEST_WIDTH);
    let zero = [BabyBear::ZERO; DIGEST_WIDTH];
    for v in pre_root.unwrap_or(zero) {
        publics.push(v);
    }
    for v in post_root {
        publics.push(v);
    }

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed ^ 0xA1A1);
    let perm16 = Perm16::new_from_rng_128(&mut rng);
    let perm24 = Perm24::new_from_rng_128(&mut rng);
    let sponge = Sponge::new(perm24.clone());
    let compress = Compress::new(perm16);
    let val_mmcs = ValMmcs::new(sponge, compress, 3);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters::new_benchmark_high_arity(challenge_mmcs);

    let dft = Dft::default();
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm24);
    let config = Config::new(pcs, challenger);

    let degree_bits = height.trailing_zeros() as usize;
    let (pp_data, pp_vk) = setup_preprocessed(&config, &air, degree_bits).expect("preprocessed");
    let proof = prove_with_preprocessed(&config, &air, trace, &publics, Some(&pp_data));
    verify_with_preprocessed(&config, &air, &proof, &publics, Some(&pp_vk)).expect("verify");
}

/// Build a Table A proof but flip the first real row's `is_s` ↔ `is_l` after
/// the witness is materialized. Must fail to verify (or fail symbolic
/// constraint checks at prove time, which is a panic — caller should run in
/// release mode).
pub fn prove_with_tampered_opcode(seed: u64, batch_size: usize) -> Result<(), ()> {
    use p3_matrix::dense::RowMajorMatrix;

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let batch: Vec<_> = (0..batch_size)
        .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
        .collect();
    let pre_root = tree.root_hash();
    let (items, proof) = tree.batch_insert(batch);
    let post_root = tree.root_hash().expect("post root");
    let mut sorted = items;
    sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

    let rows = build_table_a::<Poseidon2Hasher>(&proof, &sorted);
    let (trace, real, height) = table_a::build_trace_babybear(&rows);
    let air = TableAAir::new(height, real);

    // Tamper: flip is_s and is_l on row 0.
    let mut data = trace.values;
    let width = trace.width;
    let row0 = &mut data[0..width];
    row0.swap(0, 1);
    let trace = RowMajorMatrix::new(data, width);

    let mut publics = Vec::with_capacity(2 * DIGEST_WIDTH);
    let zero = [BabyBear::ZERO; DIGEST_WIDTH];
    for v in pre_root.unwrap_or(zero) {
        publics.push(v);
    }
    for v in post_root {
        publics.push(v);
    }

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed ^ 0xA1A1);
    let perm16 = Perm16::new_from_rng_128(&mut rng);
    let perm24 = Perm24::new_from_rng_128(&mut rng);
    let sponge = Sponge::new(perm24.clone());
    let compress = Compress::new(perm16);
    let val_mmcs = ValMmcs::new(sponge, compress, 3);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters::new_benchmark_high_arity(challenge_mmcs);
    let dft = Dft::default();
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm24);
    let config = Config::new(pcs, challenger);

    let degree_bits = height.trailing_zeros() as usize;
    let (pp_data, pp_vk) = setup_preprocessed(&config, &air, degree_bits).expect("preprocessed");
    let proof = prove_with_preprocessed(&config, &air, trace, &publics, Some(&pp_data));
    match verify_with_preprocessed(&config, &air, &proof, &publics, Some(&pp_vk)) {
        Ok(()) => Ok(()),
        Err(_) => Err(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_a_proves_and_verifies() {
        prove_and_verify_table_a(7, 16);
    }

    /// Tampering invalidates the proof. Runs in release-mode CI to avoid the
    /// debug-mode `check_constraints` panic at prove-time.
    #[cfg(not(debug_assertions))]
    #[test]
    fn table_a_tampered_proof_rejected() {
        assert!(prove_with_tampered_opcode(7, 16).is_err());
    }
}
