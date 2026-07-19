//! Verifier-owned protocol identifier and frozen configuration (R3-D4,
//! `DEVPLAN-R3.md` §6.1). None of these values may be chosen by a prover: they
//! are fixed here and bound into the Fiat–Shamir transcript before any challenge
//! (see `envelope::statement_bytes`).

/// The one production R3 protocol. A benchmark-only configuration must be a
/// *different* Rust value/tag and cannot decode as this one (M2 exit criterion).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProtocolId {
    /// Fixed R3 AIR set `A/B/L/J/O/R/P`, BabyBear + quartic extension, Poseidon2
    /// commitment/transcript, and the frozen FRI parameters below.
    R3Poseidon2,
}

impl ProtocolId {
    /// Stable 8-byte on-the-wire tag. Changing the protocol in any way
    /// (`§6.1`) must change this tag. Absorbed into the transcript, not merely
    /// informational.
    pub const fn tag(self) -> [u8; 8] {
        match self {
            // ASCII "R3P2v002" — v002 = M10 no-grinding FRI (116 queries, 0 PoW).
            ProtocolId::R3Poseidon2 => *b"R3P2v002",
        }
    }

    /// Decode a wire tag back to a protocol, rejecting any unknown/benchmark tag.
    pub fn from_tag(tag: &[u8; 8]) -> Option<Self> {
        if *tag == ProtocolId::R3Poseidon2.tag() {
            Some(ProtocolId::R3Poseidon2)
        } else {
            None
        }
    }
}

/// Frozen FRI parameters (no prover-chosen `ProverConfig`). Matches the M0
/// baseline; the final choice is fixed in M10 and its change bumps the protocol
/// tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FriConfig {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub query_pow_bits: usize,
    pub max_log_arity: usize,
    pub log_final_poly_len: usize,
}

/// The frozen FRI parameters (`04-soundness-budget.md`, `09-m10-fri-grid.md`):
/// 116-bit conjectured standalone, ≥100-bit total at the frozen max shape. M10
/// selected the **no-grinding** candidate — 116 queries, 0 PoW — which proves
/// faster than the old `100 queries + 16 PoW` and is recursion-friendly.
pub const R3_FRI: FriConfig = FriConfig {
    log_blowup: 1,
    num_queries: 116,
    query_pow_bits: 0,
    max_log_arity: 3,
    log_final_poly_len: 0,
};

/// Fixed seed for deterministic derivation of the width-16/24 Poseidon2
/// commitment/challenger constants. It is a **protocol constant**, not a caller
/// input: the constants are a deterministic function of the protocol tag, so no
/// `prove`/`verify` API accepts a seed (R3-D4). Changing it bumps the tag.
pub const R3_POSEIDON2_CONST_SEED: u64 = 0x5253_4d54_5233_0001; // "RSMTR3\0\1"

/// Maximum log₂ padded table height accepted before allocation
/// (`04-soundness-budget.md`: `N_max = 2^16`). Raising it is a security change.
pub const MAX_LOG_HEIGHT: u32 = 16;

/// Documented conjectured standalone STARK/FRI soundness bits.
pub const STANDALONE_SOUNDNESS_BITS: usize =
    R3_FRI.log_blowup * R3_FRI.num_queries + R3_FRI.query_pow_bits;

const _: () = assert!(STANDALONE_SOUNDNESS_BITS >= 116, "R3-D13 standalone target");
