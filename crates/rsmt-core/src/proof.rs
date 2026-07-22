//! Consistency-proof opcode set (D7) and the compact v6a stack-machine
//! verifier — a faithful port of `rsmt6a.py::verify_consistency`.
//!
//! The verifier is the differential oracle for the whole workspace, so every
//! rejection reason is a distinct typed error the AIR negative tests can assert
//! on.

use crate::hasher::Hasher;
use crate::limbs::{KEY_BITS, Key, Value32, is_canonical_region, key_bit, region_limbs};

/// A post-order consistency-proof opcode (D7 — exactly the rsmt6a.py set).
///
/// Regions and keys are MSB-first limbs (D2/D3); `N` carries **no** region —
/// it is derived from authenticated child advice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op<D> {
    /// Opaque preserved subtree. Admissible only under a pre-existing junction.
    /// Never carries the empty digest (D6).
    S(D),
    /// Preserved junction, opened one level: `(depth, region, c_l, c_r)`.
    O {
        depth: u16,
        region: Key,
        c_l: D,
        c_r: D,
    },
    /// Preserved leaf, opened: `(key, value)`.
    OL { key: Key, value: Value32 },
    /// New leaf; `(key, value)` is consumed from the sorted batch.
    L,
    /// Junction over the two preceding stack entries at bifurcation `depth`.
    N { depth: u16 },
}

/// Every distinct reason [`verify_consistency`] rejects a stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// Empty batch but `old_root != new_root` or the proof was non-empty.
    EmptyBatchMismatch,
    /// Batch keys are not strictly increasing (duplicate or unsorted key).
    BatchNotSorted,
    /// `S` carried the empty digest, which is forbidden (D6).
    EmptyOpaque,
    /// A depth operand was out of range (`d ≥ 256`).
    BadDepth,
    /// An `O` region was not canonical (carried bits at/below its depth).
    NonCanonicalRegion,
    /// `L` requested a batch element past the end of the batch.
    BatchExhausted,
    /// `N` popped from a stack with fewer than two entries.
    StackUnderflow,
    /// An advised child had `delta ≤ d` (edge does not descend).
    CoherenceDepth,
    /// An advised child's region bit at `d` disagreed with its side.
    SideMismatch,
    /// The two advised children derived different regions.
    RegionDisagree,
    /// No child carried advice, so the region is undefined.
    NoAdvice,
    /// A new junction (`b11 = 0`) had a child without advice (confinement).
    ConfinementViolation,
    /// The batch was not fully consumed.
    LeftoverBatch,
    /// The stream ended with a stack size other than 1.
    BadFinalStack,
    /// The final `(old, new)` did not equal `(old_root, new_root)`.
    RootMismatch,
}

/// Advice describing the top node of a stacked subtree: `(depth, region)`.
/// `None` denotes an opaque subtree (`⊥`).
type Advice = Option<(u16, Key)>;

/// Stack entry: `(old_digest, new_digest, advice)`.
type Entry<D> = (Option<D>, D, Advice);

/// Compact v6a stack-machine verifier. Accepts iff `proof` rebuilds
/// `(old_root, new_root)` from `batch` under the coherence + confinement +
/// four-way rules.
///
/// `batch` is `(key_limbs, value)` pairs with exact 32-byte values; it is sorted
/// internally and required to have strictly increasing keys (D: sortedness /
/// distinctness is the prover's convenience, but the verifier still rejects a
/// batch that is not a valid ordering, matching rsmt6a.py).
///
/// **Existential-batch semantics (R3, `docs/r3/02-relation-and-extraction.md`).**
/// This CPU verifier takes the batch explicitly, but the R3 *public statement*
/// does not: the STARK proves only "there exists a canonical batch producing this
/// `(old_root, new_root)` transition." By Lemma B
/// (`docs/r3/03-rsmt-append-only.md`) the batch is exactly the strictly-increasing
/// key subsequence of the `L` opcodes, forced by post-order topology + coherence —
/// so R3 extracts it rather than trusting an external sorted list. The internal
/// `sort` below is convenience, never trusted verifier preprocessing.
pub fn verify_consistency<H: Hasher>(
    proof: &[Op<H::Digest>],
    old_root: Option<&H::Digest>,
    new_root: &H::Digest,
    batch: &[(Key, Value32)],
) -> Result<(), VerifyError> {
    if batch.is_empty() {
        // D6: the empty-batch identity transition is the caller's job; the
        // verifier only accepts an empty proof with old_root == new_root.
        return if proof.is_empty() && old_root == Some(new_root) {
            Ok(())
        } else {
            Err(VerifyError::EmptyBatchMismatch)
        };
    }

    // Strictly increasing keys (rejects duplicates and unsorted input).
    let mut sorted: Vec<&(Key, Value32)> = batch.iter().collect();
    sorted.sort_by_key(|a| a.0);
    for w in sorted.windows(2) {
        if w[0].0 >= w[1].0 {
            return Err(VerifyError::BatchNotSorted);
        }
    }

    let mut stack: Vec<Entry<H::Digest>> = Vec::new();
    let mut bi = 0usize;

    for op in proof {
        match op {
            Op::S(h) => {
                stack.push((Some(h.clone()), h.clone(), None));
            }
            Op::O {
                depth,
                region,
                c_l,
                c_r,
            } => {
                if *depth >= KEY_BITS {
                    return Err(VerifyError::BadDepth);
                }
                if !is_canonical_region(region, *depth) {
                    return Err(VerifyError::NonCanonicalRegion);
                }
                let h = H::hash_node(*depth, region, c_l, c_r);
                stack.push((Some(h.clone()), h, Some((*depth, *region))));
            }
            Op::OL { key, value } => {
                let h = H::hash_leaf(key, value);
                stack.push((Some(h.clone()), h, Some((KEY_BITS, *key))));
            }
            Op::L => {
                let Some((k, v)) = sorted.get(bi) else {
                    return Err(VerifyError::BatchExhausted);
                };
                bi += 1;
                let h = H::hash_leaf(k, v);
                stack.push((None, h, Some((KEY_BITS, *k))));
            }
            Op::N { depth } => {
                let d = *depth;
                if d >= KEY_BITS {
                    return Err(VerifyError::BadDepth);
                }
                let right = stack.pop().ok_or(VerifyError::StackUnderflow)?;
                let left = stack.pop().ok_or(VerifyError::StackUnderflow)?;
                let (lh0, lh1, ladv) = left;
                let (rh0, rh1, radv) = right;

                // Derive p from every advised child; children must agree and
                // each described edge must be coherent (δ > d, ρ[d] = side).
                let mut p: Option<Key> = None;
                for (adv, side) in [(&ladv, 0u32), (&radv, 1u32)] {
                    let Some((delta, rho)) = adv else { continue };
                    if *delta <= d {
                        return Err(VerifyError::CoherenceDepth);
                    }
                    if key_bit(rho, d) != side {
                        return Err(VerifyError::SideMismatch);
                    }
                    let candidate = region_limbs(rho, d);
                    if let Some(prev) = p
                        && prev != candidate
                    {
                        return Err(VerifyError::RegionDisagree);
                    }
                    p = Some(candidate);
                }
                let Some(p) = p else {
                    return Err(VerifyError::NoAdvice);
                };

                let is_new = lh0.is_none() || rh0.is_none();
                if is_new && (ladv.is_none() || radv.is_none()) {
                    return Err(VerifyError::ConfinementViolation);
                }

                // Four-way old-state rule.
                let h0 = match (lh0, rh0) {
                    (None, None) => None,
                    (None, Some(r)) => Some(r),
                    (Some(l), None) => Some(l),
                    (Some(l), Some(r)) => Some(H::hash_node(d, &p, &l, &r)),
                };
                let h1 = H::hash_node(d, &p, &lh1, &rh1);
                stack.push((h0, h1, Some((d, p))));
            }
        }
    }

    if bi != sorted.len() {
        return Err(VerifyError::LeftoverBatch);
    }
    if stack.len() != 1 {
        return Err(VerifyError::BadFinalStack);
    }
    let (h0, h1, _) = stack.pop().unwrap();
    if h0.as_ref() != old_root || &h1 != new_root {
        return Err(VerifyError::RootMismatch);
    }
    Ok(())
}
