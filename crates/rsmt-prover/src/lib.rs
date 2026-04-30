//! Prover wiring around `p3-uni-stark` and `p3-fri` for RSMT3 AIRs.
//!
//! Exposes standalone demos for individual tables plus the six-AIR
//! `prove_batch` wiring with LogUp buses.

pub mod batch_demo;
pub mod config;
pub mod poseidon2_demo;
pub mod proof_hash;
pub mod table_a_demo;
pub mod table_f_demo;
pub mod tamper;
