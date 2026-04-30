//! End-to-end FRI proof of Table F's local constraints (no LogUp yet).

use num_bigint::BigUint;
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    StarkConfig, prove_with_preprocessed, setup_preprocessed, verify_with_preprocessed,
};
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_air::{TableFAir, table_f_mod};
use rsmt_core::{Tree, get_sort_key};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::build_table_f;

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

pub fn prove_and_verify_table_f(seed: u64, batch_size: usize) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let batch: Vec<_> = (0..batch_size)
        .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
        .collect();
    let (items, proof) = tree.batch_insert(batch);
    let mut sorted = items;
    sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

    let rows = build_table_f::<Poseidon2Hasher>(&proof, &sorted);
    let (trace, real, height) = table_f_mod::build_trace_babybear(&rows);
    let air = TableFAir::new(height, real);

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed ^ 0xF1F1);
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
    let publics: Vec<F> = vec![];
    let proof = prove_with_preprocessed(&config, &air, trace, &publics, Some(&pp_data));
    verify_with_preprocessed(&config, &air, &proof, &publics, Some(&pp_vk)).expect("verify");
}

/// Build Table F but mutate one b11 selector. Must fail to verify.
pub fn prove_with_tampered_b11(seed: u64, batch_size: usize) -> Result<(), ()> {
    use p3_matrix::dense::RowMajorMatrix;

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let batch: Vec<_> = (0..batch_size)
        .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
        .collect();
    let (items, proof) = tree.batch_insert(batch);
    let mut sorted = items;
    sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));
    let rows = build_table_f::<Poseidon2Hasher>(&proof, &sorted);
    let (trace, real, height) = table_f_mod::build_trace_babybear(&rows);
    let air = TableFAir::new(height, real);

    // Tamper b11 on row 0 (column 57).
    let mut data = trace.values;
    let width = trace.width;
    use p3_field::PrimeCharacteristicRing;
    let original = data[57];
    data[57] = if original == BabyBear::ZERO {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    let trace = RowMajorMatrix::new(data, width);

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed ^ 0xF1F1);
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
    let publics: Vec<F> = vec![];
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
    fn table_f_proves_and_verifies() {
        prove_and_verify_table_f(11, 16);
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn table_f_tampered_b11_rejected() {
        assert!(prove_with_tampered_b11(11, 16).is_err());
    }
}
