//! Prover wiring around `p3-batch-stark` for the R3 RSMT AIRs.
//!
//! [`r3round::prove_r3_round`] proves the seven R3 tables (`A/B/L/J/O/R/P`) for
//! one round through the real FRI stack; [`r3round::verify_r3_round`] verifies
//! it from only the proof, the public inputs, and the scalar shape — rebuilding
//! the AIRs and preprocessing itself (verifier-independent). The FRI/transcript
//! proof hash is selectable (`proof_hash`), independent of the in-circuit
//! Poseidon2.

pub mod config;
pub mod proof_hash;
pub mod r3round;

#[cfg(test)]
mod logup_pairing;

pub use config::ProverConfig;
pub use proof_hash::{
    Blake3ProofHash, Poseidon2ProofHash, ProvingHash, ProvingHashSuite, Sha256ProofHash,
};
pub use r3round::{
    R3RoundTraces, R3TableCells, prove_and_verify_r3_round, prove_and_verify_r3_round_with,
    prove_r3_round, r3_round_cells, round_shape, verify_r3_round,
};
