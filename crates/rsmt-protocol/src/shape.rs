//! Canonical public round shape: **scalar counts only** (R3-D6, no per-request
//! `Vec<bool>`). The verifier recomputes every padded height and checks the
//! count identities, the maximum-height bound, and the per-bus no-wrap formulas
//! *before* allocating (`DEVPLAN-R3.md` §6.2, `docs/r3/04-soundness-budget.md`).

use crate::codec::{BABYBEAR_ORDER, DecodeError, Reader};
use crate::protocol::MAX_LOG_HEIGHT;

/// Fixed number of Poseidon2 lanes in the vectorized Table B (an M10 parameter;
/// fixed here, its change bumps the protocol tag).
pub const B_VECTOR_LEN: usize = 8;

/// Fixed heights of the protocol-constant tables.
pub const TABLE_R_HEIGHT: usize = 2048;
pub const TABLE_P_HEIGHT: usize = 32;

/// Per-table real-row counts for one non-empty round. Scalar only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RoundShape {
    /// Total opcodes = Table A real rows (`n_S + n_open + n_Ol + n_L + n_join`).
    pub n_ops: usize,
    /// New + opened leaves = Table L real rows (`n_L + n_Ol`).
    pub n_leaf: usize,
    /// Junctions = Table J real rows.
    pub n_join: usize,
    /// Openings = Table O real rows.
    pub n_open: usize,
    /// Junctions whose old state re-hashes both children (`b11`), `<= n_join`.
    pub n_b11: usize,
    /// Feed-forward Poseidon2 occurrences.
    pub n_p2ff: usize,
    /// Terminal Poseidon2 occurrences.
    pub n_p2term: usize,
}

/// Padded (power-of-two) heights the verifier derives from a valid shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaddedHeights {
    pub a: usize,
    pub b: usize,
    pub l: usize,
    pub j: usize,
    pub o: usize,
    pub r: usize,
    pub p: usize,
}

fn pad(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

impl RoundShape {
    /// Exact logical permutation count (`n_perm = n_p2ff + n_p2term`).
    pub fn n_perm(&self) -> usize {
        self.n_p2ff + self.n_p2term
    }

    /// Validate every count identity, the max-height bound, and no-wrap. This is
    /// the gate that must run before any allocation.
    pub fn validate(&self) -> Result<PaddedHeights, DecodeError> {
        let s = self;

        // A non-empty round has at least one opcode; the empty round is the
        // separate IdentityTransition, never a RoundShape.
        if s.n_ops == 0 {
            return Err(DecodeError::InvalidShape);
        }

        // Structural bounds.
        if s.n_b11 > s.n_join {
            return Err(DecodeError::InvalidShape);
        }
        // A carries one row per opcode, and S rows exist too, so:
        //   n_ops = n_S + n_open + n_leaf + n_join  ≥  n_leaf + n_join + n_open.
        let sum = s
            .n_leaf
            .checked_add(s.n_join)
            .and_then(|x| x.checked_add(s.n_open))
            .ok_or(DecodeError::InvalidShape)?;
        if sum > s.n_ops {
            return Err(DecodeError::InvalidShape);
        }

        // Exact Poseidon2 occurrence identities (04-soundness-budget §4/§5).
        //   p2ff   = 2·n_leaf + n_join + n_open
        //   p2term =   n_leaf + n_join + n_b11 + n_open
        let expect_ff = 2 * s.n_leaf + s.n_join + s.n_open;
        let expect_term = s.n_leaf + s.n_join + s.n_b11 + s.n_open;
        if s.n_p2ff != expect_ff || s.n_p2term != expect_term {
            return Err(DecodeError::InvalidShape);
        }

        // Padded heights.
        let heights = PaddedHeights {
            a: pad(s.n_ops),
            b: pad(s.n_perm().div_ceil(B_VECTOR_LEN)),
            l: pad(s.n_leaf),
            j: pad(s.n_join),
            o: pad(s.n_open),
            r: TABLE_R_HEIGHT,
            p: TABLE_P_HEIGHT,
        };
        let max = 1usize << MAX_LOG_HEIGHT;
        for h in [heights.a, heights.b, heights.l, heights.j, heights.o] {
            if h > max {
                return Err(DecodeError::InvalidShape);
            }
        }

        // Per-bus no-wrap: every bus's max total multiplicity `< p`
        // (04-soundness-budget §5). Use u64 to avoid intermediate overflow.
        let p = BABYBEAR_ORDER as u64;
        let leaf = s.n_leaf as u64;
        let join = s.n_join as u64;
        let open = s.n_open as u64;
        // range bus: 52 digits/leaf + ≤30/join + ≤30/open (conservative caps).
        let m_range = 52 * leaf + 30 * join + 30 * open;
        // p2 buses: total occurrences.
        let m_p2 = s.n_perm() as u64;
        // others are ≤ 1 per row: bounded by n_ops.
        let m_row = s.n_ops as u64;
        for m in [m_range, m_p2, m_row] {
            if m >= p {
                return Err(DecodeError::InvalidShape);
            }
        }

        Ok(heights)
    }

    /// Canonical LE encoding (seven `u64` counts).
    pub fn encode(&self, out: &mut Vec<u8>) {
        for f in [
            self.n_ops,
            self.n_leaf,
            self.n_join,
            self.n_open,
            self.n_b11,
            self.n_p2ff,
            self.n_p2term,
        ] {
            out.extend_from_slice(&(f as u64).to_le_bytes());
        }
    }

    /// Decode seven `u64` counts. Does **not** validate; call [`validate`] next.
    ///
    /// [`validate`]: RoundShape::validate
    pub fn decode(r: &mut Reader<'_>) -> Result<Self, DecodeError> {
        let rd = |r: &mut Reader<'_>| -> Result<usize, DecodeError> {
            // Counts are bounded well below usize::MAX; read as u64.
            Ok(r.read_u64()? as usize)
        };
        Ok(RoundShape {
            n_ops: rd(r)?,
            n_leaf: rd(r)?,
            n_join: rd(r)?,
            n_open: rd(r)?,
            n_b11: rd(r)?,
            n_p2ff: rd(r)?,
            n_p2term: rd(r)?,
        })
    }
}
