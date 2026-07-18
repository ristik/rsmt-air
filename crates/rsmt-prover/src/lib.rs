//! Prover wiring around `p3-batch-stark` for the RSMT v6a AIRs (DEVPLAN M4).
//!
//! `prove_and_verify_round` proves all seven table AIRs for one round through
//! the real FRI stack and verifies the result. The FRI/transcript proof hash is
//! selectable (`proof_hash`), independent of the in-circuit Poseidon2.

pub mod config;
pub mod proof_hash;
pub mod round;
#[cfg(test)]
mod tamper;

pub use config::ProverConfig;
pub use proof_hash::{
    Blake3ProofHash, Poseidon2ProofHash, ProvingHash, ProvingHashSuite, Sha256ProofHash,
};
pub use round::{
    RoundMetrics, RoundShape, TableMetric, prove_and_verify_round, prove_and_verify_round_metrics,
};

#[cfg(test)]
mod tests;
