//! Compile-time selectable hash suites for the proving PCS and transcript.
//!
//! These hashes are internal to the STARK proof system: Merkle commitments for
//! traces/quotients/FRI rounds and Fiat-Shamir challenges. They are independent
//! from the RSMT hash checked by the AIR (`rsmt-hash::Poseidon2Hasher`).

use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_blake3::Blake3;
use p3_challenger::{DuplexChallenger, HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::Field;
use p3_field::extension::BinomialExtensionField;
use p3_fri::TwoAdicFriPcs;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_sha256::Sha256;
use p3_symmetric::{
    CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher, TruncatedPermutation,
};
use p3_uni_stark::{StarkConfig, StarkGenericConfig};
use rand::SeedableRng;
use rand_xoshiro::Xoshiro256PlusPlus;

use crate::config::ProverConfig;

pub type F = BabyBear;
pub type EF = BinomialExtensionField<F, 4>;
pub type Dft = Radix2DitParallel<F>;

pub trait ProvingHashSuite: Copy + Clone + 'static {
    type Config: StarkGenericConfig<Challenge = EF> + Clone;

    const NAME: &'static str;

    fn build_config(seed: u64, cfg: &ProverConfig) -> Self::Config;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Poseidon2ProofHash;

type Perm16 = Poseidon2BabyBear<16>;
type Perm24 = Poseidon2BabyBear<24>;
type Poseidon2Sponge = PaddingFreeSponge<Perm24, 24, 16, 8>;
type Poseidon2Compress = TruncatedPermutation<Perm16, 2, 8, 16>;
pub type Poseidon2ValMmcs = MerkleTreeMmcs<
    <F as Field>::Packing,
    <F as Field>::Packing,
    Poseidon2Sponge,
    Poseidon2Compress,
    2,
    8,
>;
pub type Poseidon2ChallengeMmcs = ExtensionMmcs<F, EF, Poseidon2ValMmcs>;
pub type Poseidon2Pcs = TwoAdicFriPcs<F, Dft, Poseidon2ValMmcs, Poseidon2ChallengeMmcs>;
pub type Poseidon2Challenger = DuplexChallenger<F, Perm24, 24, 16>;
pub type Poseidon2Config = StarkConfig<Poseidon2Pcs, EF, Poseidon2Challenger>;

impl ProvingHashSuite for Poseidon2ProofHash {
    type Config = Poseidon2Config;

    const NAME: &'static str = "poseidon2";

    fn build_config(seed: u64, cfg: &ProverConfig) -> Self::Config {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed ^ 0xBEEF);
        let perm16 = Perm16::new_from_rng_128(&mut rng);
        let perm24 = Perm24::new_from_rng_128(&mut rng);
        let sponge = Poseidon2Sponge::new(perm24.clone());
        let compress = Poseidon2Compress::new(perm16);
        let val_mmcs = Poseidon2ValMmcs::new(sponge, compress, 3);
        let challenge_mmcs = Poseidon2ChallengeMmcs::new(val_mmcs.clone());
        let fri_params = cfg.to_fri_params(challenge_mmcs);
        let pcs = Poseidon2Pcs::new(Dft::default(), val_mmcs, fri_params);
        let challenger = Poseidon2Challenger::new(perm24);
        Poseidon2Config::new(pcs, challenger)
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Sha256ProofHash;

type Sha256FieldHash = SerializingHasher<Sha256>;
type Sha256Compress = CompressionFunctionFromHasher<Sha256, 2, 32>;
pub type Sha256ValMmcs = MerkleTreeMmcs<F, u8, Sha256FieldHash, Sha256Compress, 2, 32>;
pub type Sha256ChallengeMmcs = ExtensionMmcs<F, EF, Sha256ValMmcs>;
pub type Sha256Pcs = TwoAdicFriPcs<F, Dft, Sha256ValMmcs, Sha256ChallengeMmcs>;
pub type Sha256Challenger = SerializingChallenger32<F, HashChallenger<u8, Sha256, 32>>;
pub type Sha256Config = StarkConfig<Sha256Pcs, EF, Sha256Challenger>;

impl ProvingHashSuite for Sha256ProofHash {
    type Config = Sha256Config;

    const NAME: &'static str = "sha256";

    fn build_config(_seed: u64, cfg: &ProverConfig) -> Self::Config {
        let byte_hash = Sha256;
        let field_hash = Sha256FieldHash::new(byte_hash);
        let compress = Sha256Compress::new(byte_hash);
        let val_mmcs = Sha256ValMmcs::new(field_hash, compress, 3);
        let challenge_mmcs = Sha256ChallengeMmcs::new(val_mmcs.clone());
        let fri_params = cfg.to_fri_params(challenge_mmcs);
        let pcs = Sha256Pcs::new(Dft::default(), val_mmcs, fri_params);
        let challenger = Sha256Challenger::from_hasher(vec![], byte_hash);
        Sha256Config::new(pcs, challenger)
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Blake3ProofHash;

type Blake3FieldHash = SerializingHasher<Blake3>;
type Blake3Compress = CompressionFunctionFromHasher<Blake3, 2, 32>;
pub type Blake3ValMmcs = MerkleTreeMmcs<F, u8, Blake3FieldHash, Blake3Compress, 2, 32>;
pub type Blake3ChallengeMmcs = ExtensionMmcs<F, EF, Blake3ValMmcs>;
pub type Blake3Pcs = TwoAdicFriPcs<F, Dft, Blake3ValMmcs, Blake3ChallengeMmcs>;
pub type Blake3Challenger = SerializingChallenger32<F, HashChallenger<u8, Blake3, 32>>;
pub type Blake3Config = StarkConfig<Blake3Pcs, EF, Blake3Challenger>;

impl ProvingHashSuite for Blake3ProofHash {
    type Config = Blake3Config;

    const NAME: &'static str = "blake3";

    fn build_config(_seed: u64, cfg: &ProverConfig) -> Self::Config {
        let byte_hash = Blake3;
        let field_hash = Blake3FieldHash::new(byte_hash);
        let compress = Blake3Compress::new(byte_hash);
        let val_mmcs = Blake3ValMmcs::new(field_hash, compress, 3);
        let challenge_mmcs = Blake3ChallengeMmcs::new(val_mmcs.clone());
        let fri_params = cfg.to_fri_params(challenge_mmcs);
        let pcs = Blake3Pcs::new(Dft::default(), val_mmcs, fri_params);
        let challenger = Blake3Challenger::from_hasher(vec![], byte_hash);
        Blake3Config::new(pcs, challenger)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProvingHash {
    Poseidon2,
    Sha256,
    Blake3,
}

impl ProvingHash {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Poseidon2 => Poseidon2ProofHash::NAME,
            Self::Sha256 => Sha256ProofHash::NAME,
            Self::Blake3 => Blake3ProofHash::NAME,
        }
    }
}

impl Default for ProvingHash {
    fn default() -> Self {
        Self::Poseidon2
    }
}
