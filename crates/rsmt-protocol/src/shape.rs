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
    ///
    /// The wire-level surface collapses every failure to the opaque
    /// [`DecodeError::InvalidShape`] (negative tests assert on it). For an
    /// operator-facing, fully-explained reason — including the soundness story
    /// behind the height cap — call [`describe_rejection`] instead.
    ///
    /// [`describe_rejection`]: RoundShape::describe_rejection
    pub fn validate(&self) -> Result<PaddedHeights, DecodeError> {
        self.check().map_err(|_| DecodeError::InvalidShape)
    }

    /// The single source of truth behind [`validate`]: every check, in order,
    /// returning a *descriptive* [`ShapeReject`] on the first failure.
    ///
    /// [`validate`]: RoundShape::validate
    fn check(&self) -> Result<PaddedHeights, ShapeReject> {
        let s = self;

        // A non-empty round has at least one opcode; the empty round is the
        // separate IdentityTransition, never a RoundShape.
        if s.n_ops == 0 {
            return Err(ShapeReject::EmptyRound);
        }

        // Structural bounds.
        if s.n_b11 > s.n_join {
            return Err(ShapeReject::B11ExceedsJoin {
                n_b11: s.n_b11,
                n_join: s.n_join,
            });
        }
        // A carries one row per opcode, and S rows exist too, so:
        //   n_ops = n_S + n_open + n_leaf + n_join  ≥  n_leaf + n_join + n_open.
        let sum = s
            .n_leaf
            .checked_add(s.n_join)
            .and_then(|x| x.checked_add(s.n_open))
            .ok_or(ShapeReject::CountOverflow)?;
        if sum > s.n_ops {
            return Err(ShapeReject::OpsTooFew {
                sum,
                n_ops: s.n_ops,
            });
        }

        // Exact Poseidon2 occurrence identities (04-soundness-budget §4/§5).
        //   p2ff   = 2·n_leaf + n_join + n_open
        //   p2term =   n_leaf + n_join + n_b11 + n_open
        let expect_ff = 2 * s.n_leaf + s.n_join + s.n_open;
        let expect_term = s.n_leaf + s.n_join + s.n_b11 + s.n_open;
        if s.n_p2ff != expect_ff {
            return Err(ShapeReject::P2Mismatch {
                bus: "p2ff",
                got: s.n_p2ff,
                expect: expect_ff,
            });
        }
        if s.n_p2term != expect_term {
            return Err(ShapeReject::P2Mismatch {
                bus: "p2term",
                got: s.n_p2term,
                expect: expect_term,
            });
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
        for (table, n, padded) in [
            ("A", s.n_ops, heights.a),
            ("B", s.n_perm().div_ceil(B_VECTOR_LEN), heights.b),
            ("L", s.n_leaf, heights.l),
            ("J", s.n_join, heights.j),
            ("O", s.n_open, heights.o),
        ] {
            if padded > max {
                return Err(ShapeReject::TableTooTall {
                    table,
                    n,
                    padded,
                    max,
                });
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
        for (bus, m) in [("range", m_range), ("p2", m_p2), ("row", m_row)] {
            if m >= p {
                return Err(ShapeReject::BusWrap { bus, m, p });
            }
        }

        Ok(heights)
    }

    /// An operator-facing explanation of *why* [`validate`] rejects this shape,
    /// or `None` if it is valid. This runs the identical gate as [`validate`]
    /// (shared [`check`]) and formats the first failing invariant. The height
    /// cap carries the full soundness rationale so an oversized batch reads as a
    /// deliberate, quantified security limit rather than an opaque failure.
    ///
    /// [`validate`]: RoundShape::validate
    /// [`check`]: RoundShape::check
    pub fn describe_rejection(&self) -> Option<String> {
        self.check().err().map(|e| e.explain())
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

/// Why a [`RoundShape`] fails [`validate`](RoundShape::validate) — one variant
/// per invariant, carrying the offending numbers. The wire API keeps collapsing
/// these to [`DecodeError::InvalidShape`]; this type only feeds the
/// human-readable [`describe_rejection`](RoundShape::describe_rejection).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ShapeReject {
    /// `n_ops == 0`: the empty round is `IdentityTransition`, not a `RoundShape`.
    EmptyRound,
    /// `n_b11 > n_join`.
    B11ExceedsJoin { n_b11: usize, n_join: usize },
    /// `n_leaf + n_join + n_open` overflowed `usize`.
    CountOverflow,
    /// `n_leaf + n_join + n_open > n_ops`.
    OpsTooFew { sum: usize, n_ops: usize },
    /// A Poseidon2 occurrence identity failed (`p2ff` or `p2term`).
    P2Mismatch {
        bus: &'static str,
        got: usize,
        expect: usize,
    },
    /// A table's padded height exceeds the frozen `N_max = 2^MAX_LOG_HEIGHT`.
    TableTooTall {
        table: &'static str,
        n: usize,
        padded: usize,
        max: usize,
    },
    /// A bus's maximum total multiplicity reaches `p` (would wrap mod `p`).
    BusWrap { bus: &'static str, m: u64, p: u64 },
}

impl ShapeReject {
    /// Format this rejection for an operator. The height cap gets the full
    /// soundness story (`docs/r3/04-soundness-budget.md`); the rest are concise
    /// statements of the violated identity.
    fn explain(&self) -> String {
        match *self {
            ShapeReject::EmptyRound => {
                "shape rejected: n_ops = 0 (an empty round must be encoded as the \
                 IdentityTransition, not a RoundShape)"
                    .to_string()
            }
            ShapeReject::B11ExceedsJoin { n_b11, n_join } => format!(
                "shape rejected: n_b11 = {n_b11} exceeds n_join = {n_join} \
                 (b11 junctions are a subset of all junctions)"
            ),
            ShapeReject::CountOverflow => {
                "shape rejected: n_leaf + n_join + n_open overflowed usize".to_string()
            }
            ShapeReject::OpsTooFew { sum, n_ops } => format!(
                "shape rejected: n_leaf + n_join + n_open = {sum} exceeds n_ops = {n_ops} \
                 (Table A carries one row per opcode, so n_ops must dominate)"
            ),
            ShapeReject::P2Mismatch { bus, got, expect } => format!(
                "shape rejected: Poseidon2 occurrence count {bus} = {got}, expected {expect} \
                 (04-soundness-budget §4 identity)"
            ),
            ShapeReject::TableTooTall {
                table,
                n,
                padded,
                max,
            } => format!(
                "shape rejected: Table {table} needs {n} rows → padded height {padded} \
                 (2^{}), over the frozen limit N_max = {max} rows (2^{}).\n\
                 \n\
                 Why this limit exists (docs/r3/04-soundness-budget.md §3):\n\
                 N_max is a hard PRE-ALLOCATION soundness gate, not a memory or \
                 performance guard. The complete false-accept probability is bounded by a \
                 union of algebraic terms over the extension field |EF| = p^4 ≈ 2^123.6:\n\
                 \x20 • ε2 (FRI commit)  ∝ N / |EF|\n\
                 \x20 • ε3 (DEEP/quotient) ∝ N / |EF|\n\
                 \x20 • ε4 (LogUp)       ∝ T·w / |EF|   (T = total interactions, w ≈ 32)\n\
                 These are independent of the FRI query count: the R3 FRI params give ~128 \
                 conjectured bits standalone, but the *complete* bound is capped by the shape. \
                 At N = 2^{} the union total is ≈ 100.5 bits (target ≥ 100); each doubling of \
                 N or T costs ≈ 1 bit, so N = 2^{} would fall to ≈ 99.6 bits — under target. \
                 Raising MAX_LOG_HEIGHT is therefore a security change that bumps the protocol \
                 tag, and the only headroom lever is a degree-5 extension field (+30 bits), a \
                 separate protocol revision.\n\
                 \n\
                 How to proceed: keep every table's real row count ≤ {max}. Table {table} is \
                 the binding one here ({n} > {max}, i.e. {}% over); split this batch into that \
                 many smaller rounds (or fewer keys each) so its count stays within the cap. \
                 Table A carries roughly one row per opcode and ~8–9 opcodes per inserted key \
                 (it grows with tree depth), so plan for well under ~{} keys per round.",
                padded.trailing_zeros(),
                max.trailing_zeros(),
                max.trailing_zeros(),
                max.trailing_zeros() + 1,
                (n * 100).div_ceil(max) - 100,
                max / 9,
            ),
            ShapeReject::BusWrap { bus, m, p } => format!(
                "shape rejected: {bus}-bus maximum total multiplicity {m} reaches the field \
                 order p = {p} and would wrap mod p, forging LogUp balance \
                 (04-soundness-budget §5)"
            ),
        }
    }
}
