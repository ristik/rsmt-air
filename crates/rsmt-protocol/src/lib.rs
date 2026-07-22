//! `rsmt-protocol` — the verifier-owned R3 protocol boundary (M2).
//!
//! This crate is deliberately **prover-independent**: it defines the fixed
//! [`ProtocolId`], the canonical field/statement/shape/envelope codecs, and the
//! pre-allocation shape validation. Nothing here can select a hash suite, seed,
//! or FRI configuration from proof bytes (R3-D4/D6), and every malformed or
//! cross-version envelope is rejected before expensive work (`DEVPLAN-R3.md`
//! §6, `docs/r3/`).
//!
//! The STARK proof itself is an opaque, length-bounded blob at this layer; the
//! opening/shape cross-check and the actual prove/verify wiring land in M7.

pub mod codec;
pub mod envelope;
pub mod identity;
pub mod protocol;
pub mod shape;

pub use codec::{BABYBEAR_ORDER, DecodeError};
pub use envelope::{MAX_STARK_BYTES, ProofEnvelope, RoundPublicInputs, statement_bytes};
pub use identity::IdentityTransition;
pub use protocol::{
    FriConfig, MAX_LOG_HEIGHT, ProtocolId, R3_FRI, R3_POSEIDON2_CONST_SEED,
    STANDALONE_SOUNDNESS_BITS,
};
pub use shape::{PaddedHeights, RoundShape};

#[cfg(test)]
mod tests;
