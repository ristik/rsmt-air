//! `build_r3_plan` (M3): lower a verified Poseidon2 consistency-proof stream into
//! the R3 row plan — reduced Table-A rows plus the fused-leaf (`R3Leaf`),
//! join (`R3Join`), and opening (`R3Open`) rows, the occurrence-correct
//! [`PermutationPlan`], and the Table-R / Table-P multiplicity tallies.
//!
//! The stream is first checked by the reference verifier (fail-fast, so the plan
//! is only ever built for an accepting execution — the extraction self-check of
//! `DEVPLAN-R3.md` M3). The reduced A row drops `batch_idx`, `opened_idx`,
//! `has_advice`, and `node_hash_old_needed` (§5.2): leaves/openings bind to A by
//! row index, advice is `1 − is_s`, and `b11` is derived by Table J.

use p3_baby_bear::BabyBear;
use rsmt_core::{Key, KeyValue, Op, VerifyError, verify_consistency};
use rsmt_hash::{Digest, Poseidon2Hasher, default_perm};

use crate::plan::OpKind;
use crate::r3arena::PermutationPlan;
use crate::r3plan::{
    JoinChild, R3Join, R3Leaf, R3Open, build_join, build_leaf, build_open, locate_depth,
};
use crate::r10::{R10_REAL, r10_index};

type F = BabyBear;

/// A reduced Table-A row: one per opcode (`DEVPLAN-R3.md` §5.2). No `batch_idx`,
/// `opened_idx`, `has_advice`, or `node_hash_old_needed`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R3ARow {
    pub row_idx: u32,
    pub kind: OpKind,
    pub old: Digest,
    pub new: Digest,
    pub old_is_none: bool,
    pub delta: u16,
    pub rho: Key,
    pub subtree_start: u32,
}

/// Scalar per-table real-row counts (mirrors `rsmt_protocol::RoundShape`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R3Shape {
    pub n_ops: usize,
    pub n_leaf: usize,
    pub n_join: usize,
    pub n_open: usize,
    pub n_b11: usize,
    pub n_p2ff: usize,
    pub n_p2term: usize,
}

/// The complete R3 witness plan for one non-empty round.
pub struct R3Plan {
    pub a_rows: Vec<R3ARow>,
    pub leaves: Vec<R3Leaf>,
    pub joins: Vec<R3Join>,
    pub opens: Vec<R3Open>,
    pub arena: PermutationPlan,
    /// Table-R (range) multiplicities, indexed by `r10_index(bits, value)`.
    pub r_mults: Vec<u32>,
    /// Table-P (pow2) multiplicities, indexed by exponent `0..=30`.
    pub p_mults: [u32; 31],
    pub old_root: Option<Digest>,
    pub new_root: Digest,
    pub old_root_is_none: bool,
    pub shape: R3Shape,
}

/// Errors from R3 plan construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R3PlanError {
    /// The stream was rejected by the reference verifier.
    Rejected(VerifyError),
    /// A per-bus multiplicity total reached the BabyBear order (would wrap).
    MultiplicityWrap,
    /// An internal structural invariant failed.
    Inconsistent(&'static str),
}

struct Entry {
    old: Option<Digest>,
    new: Digest,
    advice: Option<(u16, Key)>,
    subtree_start: u32,
    row_idx: u32,
}

/// BabyBear order (for the no-wrap check).
const BABYBEAR_ORDER: u32 = 0x7800_0001;

/// Build the R3 plan from a verified stream.
pub fn build_r3_plan(
    proof: &[Op<Digest>],
    batch: &[KeyValue],
    old_root: Option<&Digest>,
    new_root: &Digest,
) -> Result<R3Plan, R3PlanError> {
    verify_consistency::<Poseidon2Hasher>(proof, old_root, new_root, batch)
        .map_err(R3PlanError::Rejected)?;

    let mut sorted: Vec<&KeyValue> = batch.iter().collect();
    sorted.sort_by_key(|kv| kv.0);

    let perm = default_perm();
    let mut arena = PermutationPlan::new();
    let mut a_rows: Vec<R3ARow> = Vec::with_capacity(proof.len());
    let mut leaves: Vec<R3Leaf> = Vec::new();
    let mut joins: Vec<R3Join> = Vec::new();
    let mut opens: Vec<R3Open> = Vec::new();
    let mut r_mults = vec![0u32; R10_REAL];
    let mut p_mults = [0u32; 31];
    let mut stack: Vec<Entry> = Vec::new();
    let mut bi = 0usize;
    let zero: Digest = [F::default(); 8];

    let tally_r = |mults: &mut [u32], recv: &[(u32, u32)]| {
        for &(bits, value) in recv {
            mults[r10_index(bits, value)] += 1;
        }
    };

    for (i, op) in proof.iter().enumerate() {
        let row_idx = i as u32;
        match op {
            Op::S(h) => {
                a_rows.push(R3ARow {
                    row_idx,
                    kind: OpKind::S,
                    old: *h,
                    new: *h,
                    old_is_none: false,
                    delta: 0,
                    rho: [0u32; 9],
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: Some(*h),
                    new: *h,
                    advice: None,
                    subtree_start: row_idx,
                    row_idx,
                });
            }
            Op::O {
                depth,
                region,
                c_l,
                c_r,
            } => {
                let (o, recv) = build_open(&perm, &mut arena, row_idx, *depth, region, c_l, c_r);
                tally_r(&mut r_mults, &recv);
                let (_, r_off, w) = locate_depth(*depth);
                p_mults[(w - r_off - 1) as usize] += 1;
                a_rows.push(R3ARow {
                    row_idx,
                    kind: OpKind::O,
                    old: o.digest,
                    new: o.digest,
                    old_is_none: false,
                    delta: *depth,
                    rho: *region,
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: Some(o.digest),
                    new: o.digest,
                    advice: Some((*depth, *region)),
                    subtree_start: row_idx,
                    row_idx,
                });
                opens.push(o);
            }
            Op::OL { key, value } => {
                let (leaf, recv) = build_leaf(&perm, &mut arena, row_idx, key, value);
                tally_r(&mut r_mults, &recv);
                let digest = leaf.digest;
                a_rows.push(R3ARow {
                    row_idx,
                    kind: OpKind::OL,
                    old: digest,
                    new: digest,
                    old_is_none: false,
                    delta: 256,
                    rho: *key,
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: Some(digest),
                    new: digest,
                    advice: Some((256, *key)),
                    subtree_start: row_idx,
                    row_idx,
                });
                leaves.push(leaf);
            }
            Op::L => {
                let (k, v) = sorted
                    .get(bi)
                    .ok_or(R3PlanError::Inconsistent("batch exhausted"))?;
                bi += 1;
                let (leaf, recv) = build_leaf(&perm, &mut arena, row_idx, k, v);
                tally_r(&mut r_mults, &recv);
                let digest = leaf.digest;
                a_rows.push(R3ARow {
                    row_idx,
                    kind: OpKind::L,
                    old: zero,
                    new: digest,
                    old_is_none: true,
                    delta: 256,
                    rho: *k,
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: None,
                    new: digest,
                    advice: Some((256, *k)),
                    subtree_start: row_idx,
                    row_idx,
                });
                leaves.push(leaf);
            }
            Op::N { depth } => {
                let right = stack
                    .pop()
                    .ok_or(R3PlanError::Inconsistent("N underflow"))?;
                let left = stack
                    .pop()
                    .ok_or(R3PlanError::Inconsistent("N underflow"))?;
                let lc = JoinChild {
                    old: left.old,
                    new: left.new,
                    advice: left.advice,
                    subtree_start: left.subtree_start,
                    row_idx: left.row_idx,
                };
                let rc = JoinChild {
                    old: right.old,
                    new: right.new,
                    advice: right.advice,
                    subtree_start: right.subtree_start,
                    row_idx: right.row_idx,
                };
                let (j, recv, k) = build_join(&perm, &mut arena, row_idx, *depth, &lc, &rc);
                tally_r(&mut r_mults, &recv);
                p_mults[k as usize] += 1;

                // Post-order contiguity (D19 / S2).
                if right.row_idx + 1 != row_idx {
                    return Err(R3PlanError::Inconsistent("post-order locality broken"));
                }
                if j.rs == 0 || left.row_idx + 1 != j.rs {
                    return Err(R3PlanError::Inconsistent("post-order subtree_start broken"));
                }
                a_rows.push(R3ARow {
                    row_idx,
                    kind: OpKind::N,
                    old: j.old_digest.unwrap_or(zero),
                    new: j.new_digest,
                    old_is_none: j.old_digest.is_none(),
                    delta: *depth,
                    rho: j.region,
                    subtree_start: j.ls,
                });
                stack.push(Entry {
                    old: j.old_digest,
                    new: j.new_digest,
                    advice: Some((*depth, j.region)),
                    subtree_start: j.ls,
                    row_idx,
                });
                joins.push(j);
            }
        }
    }

    if stack.len() != 1 {
        return Err(R3PlanError::Inconsistent("final stack size != 1"));
    }

    let n_b11 = joins.iter().filter(|j| j.b11).count();
    let shape = R3Shape {
        n_ops: a_rows.len(),
        n_leaf: leaves.len(),
        n_join: joins.len(),
        n_open: opens.len(),
        n_b11,
        n_p2ff: arena.n_ff(),
        n_p2term: arena.n_term(),
    };

    // Per-bus no-wrap: the binding total is the range bus.
    let range_total: u64 = r_mults.iter().map(|&m| m as u64).sum();
    let pow_total: u64 = p_mults.iter().map(|&m| m as u64).sum();
    if range_total >= BABYBEAR_ORDER as u64 || pow_total >= BABYBEAR_ORDER as u64 {
        return Err(R3PlanError::MultiplicityWrap);
    }

    Ok(R3Plan {
        a_rows,
        leaves,
        joins,
        opens,
        arena,
        r_mults,
        p_mults,
        old_root: old_root.copied(),
        new_root: *new_root,
        old_root_is_none: old_root.is_none(),
        shape,
    })
}

/// Structural invariants beyond what `build_r3_plan` already enforces: exact
/// permutation occurrence budget and shape self-consistency.
pub fn check_r3_invariants(plan: &R3Plan) -> Result<(), &'static str> {
    let s = &plan.shape;
    if plan.a_rows.len() != s.n_ops || plan.leaves.len() != s.n_leaf {
        return Err("a_rows/leaves count mismatch");
    }
    if plan.joins.len() != s.n_join || plan.opens.len() != s.n_open {
        return Err("joins/opens count mismatch");
    }
    plan.arena
        .verify_counts(s.n_leaf, s.n_join, s.n_open, s.n_b11)?;
    // Every non-root A row is consumed once; the root has subtree_start 0.
    if let Some(root) = plan.a_rows.last()
        && root.subtree_start != 0
    {
        return Err("root subtree_start != 0");
    }
    Ok(())
}

#[cfg(test)]
mod tests;
