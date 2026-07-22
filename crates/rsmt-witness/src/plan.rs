//! Out-of-circuit preprocessing (DEVPLAN M2).
//!
//! A single walk of the Poseidon2 consistency-proof stream produces a
//! [`TracePlan`]: everything data-dependent — post-order pointers, case bits,
//! derived regions, the boundary-limb coherence split, the deduplicated
//! permutation arena, and the byte / power-of-two multiplicity tallies — so
//! that M3's trace generation is a straight, data-independent fill.
//!
//! The plan is **self-validated** against `rsmt-core::verify_consistency`
//! before it is trusted: any mismatch is a witness-generator bug, not a proof
//! failure (DEVPLAN completeness guard).
//!
//! Column layouts (the exact AIR structs) land in M3; this module produces the
//! typed row data they will be filled from. Where a range-check decomposition
//! is an M3 layout decision (the `hi`/`lo` chunking of the boundary limb), the
//! plan records the raw values and defers the chunk multiplicities — the
//! well-defined receivers (depths, depth gaps, power-of-two shifts) are tallied
//! exactly so [`check_plan_invariants`] can assert totals against them.

use std::collections::HashMap;

use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;

use rsmt_core::{
    KEY_BITS, Key, KeyValue, Op, VerifyError, region_limbs, split_limb, verify_consistency,
};

use crate::r10::{R10_REAL, canonical_limb, r10_index, radix1024, variable_range};
use rsmt_hash::{
    Digest, PermIo, Poseidon2Hasher, State, default_perm, digest_of, leaf_perm_io, limbs_to_field,
    node_children_io, node_prefix_io, value_field_limbs,
};

type F = BabyBear;

/// Locate the boundary limb of junction depth `d`: `(q, r, w)` where `q` is the
/// limb index holding bit `d`, `r` the intra-limb offset (MSB = 0), and `w` the
/// limb width. Mirrors the key encoding; `d < 256`.
fn boundary(d: u16) -> (usize, u16, u16) {
    debug_assert!(d < KEY_BITS);
    if d < 240 {
        ((d / 30) as usize, d % 30, 30)
    } else {
        (8, d - 240, 16)
    }
}

// ---------------------------------------------------------------------------
// Permutation arena
// ---------------------------------------------------------------------------

/// Deduplicated store of Poseidon2 evaluations. Rows reference entries by
/// index; Table B is this arena chunked 8 lanes per row (M3). Prefix blocks are
/// naturally shared between the old-side and new-side children of one junction
/// because they have identical inputs.
#[derive(Default, Debug)]
pub struct Arena {
    entries: Vec<PermIo>,
    /// Per-entry Bus-2 tag (D17): `true` = feed-forward (its full 16-limb output
    /// is another sponge block's input, e.g. a node prefix or a non-final leaf
    /// step); `false` = terminal (only the 8-limb digest is used). Table B emits
    /// this as a preprocessed column so the tagged tuple keeps degree 1.
    modes: Vec<bool>,
    index: HashMap<[u32; 16], u32>,
}

fn canon(s: &State) -> [u32; 16] {
    core::array::from_fn(|i| s[i].as_canonical_u32())
}

impl Arena {
    /// Intern one evaluation with its Bus-2 `mode` (see [`Arena::modes`]),
    /// returning its arena index. Identical inputs collapse to one entry
    /// (Poseidon2 is a function, so outputs agree); a mode conflict on a
    /// collapsed entry is a builder bug (feed-forward and terminal permutations
    /// never share an input).
    pub fn intern(&mut self, io: PermIo, mode: bool) -> u32 {
        let key = canon(&io.input);
        if let Some(&i) = self.index.get(&key) {
            debug_assert_eq!(self.entries[i as usize].output, io.output);
            debug_assert_eq!(self.modes[i as usize], mode, "arena entry mode conflict");
            return i;
        }
        let i = self.entries.len() as u32;
        self.entries.push(io);
        self.modes.push(mode);
        self.index.insert(key, i);
        i
    }

    pub fn entries(&self) -> &[PermIo] {
        &self.entries
    }

    /// Per-entry feed-forward (`true`) / terminal (`false`) Bus-2 tags.
    pub fn modes(&self) -> &[bool] {
        &self.modes
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Row structs
// ---------------------------------------------------------------------------

/// Which opcode a Table A row carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpKind {
    S,
    O,
    OL,
    L,
    N,
}

/// A Table A row: one per opcode. Digest columns are received from the backing
/// helper over a bus in-circuit; here they carry the concrete values.
#[derive(Clone, Debug)]
pub struct ARow {
    pub row_idx: u32,
    pub kind: OpKind,
    pub old: Digest,
    pub new: Digest,
    pub old_is_none: bool,
    // advice tuple (has_advice, delta, rho[9])
    pub has_advice: bool,
    pub delta: u16,
    pub rho: Key,
    // opcode-specific links
    pub batch_idx: u32,             // L: index into the sorted batch / D / C-batch
    pub node_hash_old_needed: bool, // N: b11
    pub opened_idx: u32,            // O: F-open row index; OL: C-opened leaf index
    /// Post-order subtree start (D19): the smallest row index in this row's
    /// subtree. Base opcodes: `= row_idx`; `N`: `= left child's subtree_start`.
    /// The root row (last real) has `subtree_start = 0`. Sent on Bus 1 (tree)
    /// and Bus 3 (parent); proves contiguous post-order algebraically.
    pub subtree_start: u32,
}

/// Coherence data for one advised child of a junction (gated by `has`
/// in-circuit). R10 scheme (D13): `ρ[q] = 2·pow_b·H + β·pow_b + L` with the
/// shared prefix `H` on `FJoin`, constant side bit `β = side`, and this child's
/// tail `L = lo` proved `< 2^k` via its radix-1024 `l_digits`.
#[derive(Clone, Copy, Debug, Default)]
pub struct ChildCoh {
    pub has: bool,
    pub side: u32, // 0 = left, 1 = right
    pub delta: u16,
    pub rho: Key,
    pub gap: u16, // delta - d - 1  (R10 (8, gap) receive)
    pub l: u32,   // tail below the side bit (the low k bits of ρ[q])
    pub l_digits: [u32; 3],
}

/// A Table F **join** row: one per `N`. R10 coherence (D13): shared prefix `H`,
/// one `pow_b` power, radix-1024 digit decompositions; `pow_a = 2·pow_b`,
/// `gap`, `right_ptr`, case bits are derived expressions in the AIR.
#[derive(Clone, Debug)]
pub struct FJoin {
    pub parent_row_idx: u32, // = the N row's A index (Bus 3 key)
    // Post-order subtree starts (D19). `ls` = left child's subtree_start (also
    // the parent's own subtree_start, sent on Bus 3); `rs` = right child's
    // subtree_start. Left child sits at row `rs − 1`; right child at
    // `parent_row_idx − 1`. Both keys are Bus-1 receives — no witnessed pointer.
    pub ls: u32,
    pub rs: u32,
    pub depth: u16,
    pub region: Key,
    // child tuples
    pub l_old: Digest,
    pub l_new: Digest,
    pub l_none: bool,
    pub r_old: Digest,
    pub r_new: Digest,
    pub r_none: bool,
    pub b11: bool,
    // R10 coherence
    pub q: usize,
    pub r_off: u16,
    pub w: u16,
    pub pow_b: u32, // 2^{w-r-1} = 2^k
    pub h: u32,     // shared prefix H (top r bits of ρ[q])
    pub h_digits: [u32; 3],
    pub u_r: [bool; 3], // one-hot boundary digit of r = 10·h_r + s_r
    pub s_r: u16,
    pub u_k: [bool; 3], // one-hot boundary digit of k = 10·h_k + s_k
    pub s_k: u16,
    pub child_l: ChildCoh,
    pub child_r: ChildCoh,
    // arena refs
    pub prefix_idx: u32,
    pub new_children_idx: u32,
    pub old_children_idx: Option<u32>, // Some iff b11
    pub old_digest: Option<Digest>,
    pub new_digest: Digest,
    // Shared prefix output for Bus 2 (D17): feed-forward, full 16 limbs. The
    // children-block digests are `new_digest`/`old_digest` (terminal, mode=0).
    pub mid: State,
}

/// A Table F **opening** row: one per `O`. Hashes `(d', p', c_l, c_r)` once and
/// returns `(h, h, (d', p'))` on Bus 3.
#[derive(Clone, Debug)]
pub struct FOpen {
    pub parent_row_idx: u32, // = the O row's A index
    pub depth: u16,
    pub region: Key, // canonical (zero-padded below depth)
    pub c_l: Digest,
    pub c_r: Digest,
    pub prefix_idx: u32,
    pub children_idx: u32,
    pub digest: Digest,
    pub mid: State,
}

/// Whether a Table C leaf run is a batch leaf (`L`) or an opened leaf (`OL`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeafKind {
    Batch,
    Opened,
}

/// A Table C leaf: three sponge steps replayed. `perm_idx[k]` references the
/// arena entry for step `k`; the sponge states are its `input`/`output`.
#[derive(Clone, Debug)]
pub struct CLeaf {
    pub kind: LeafKind,
    pub idx: u32, // batch index (Batch) or opened-leaf index (Opened)
    pub key: [F; 9],
    pub value: [F; 9],
    pub digest: Digest,
    pub perm_idx: [u32; 3],
}

/// A Table D row: one per sorted-batch element.
#[derive(Clone, Debug)]
pub struct DRow {
    pub idx: u32,
    pub key: [F; 9],
    pub value: [F; 9],
}

/// Public boundary values (D6: `None` old root ↔ canonical all-zero digest).
#[derive(Clone, Debug)]
pub struct Publics {
    pub old_root: Digest,
    pub old_root_is_none: bool,
    pub new_root: Digest,
}

/// Per-table real-row counts — part of the public statement (fixes preprocessed
/// traces). All are `pub` and travel with the proof in M4.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    pub n_ops: usize,
    pub n_s: usize,
    pub n_open: usize, // O opcodes / F opening rows
    pub n_ol: usize,
    pub n_l: usize,
    pub n_join: usize, // N opcodes / F join rows
    pub n_b11: usize,
    pub n_batch: usize, // = n_l
    pub n_perms: usize, // arena length
}

/// The full trace plan produced by one walk of the opcode stream.
#[derive(Debug)]
pub struct TracePlan {
    pub publics: Publics,
    pub shape: Shape,
    pub a_rows: Vec<ARow>,
    pub f_joins: Vec<FJoin>,  // segmented: all join rows (D8)
    pub f_opens: Vec<FOpen>,  // then all opening rows
    pub c_batch: Vec<CLeaf>,  // segmented: batch leaves
    pub c_opened: Vec<CLeaf>, // then opened leaves
    pub d_rows: Vec<DRow>,
    pub arena: Arena,
    /// Table-R (`R10`) per-entry receive counts, indexed by [`r10_index`].
    pub r_mults: Vec<u32>,
    pub p_mults: [u32; 31],
}

/// A witness-generation failure. `Inconsistent` means the plan disagreed with
/// the reference verifier — a builder bug (should never happen on honest input).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlanError {
    /// The stream did not verify against the reference core.
    Rejected(VerifyError),
    /// The plan's recomputation disagreed with the reference verifier.
    Inconsistent(&'static str),
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// Simulated stack entry during the walk.
struct Entry {
    old: Option<Digest>,
    new: Digest,
    advice: Option<(u16, Key)>,
    row_idx: u32,
    subtree_start: u32,
}

/// Build the trace plan for a Poseidon2 consistency proof over `batch`, with
/// the public `(old_root, new_root)`. Self-validates against the reference
/// verifier before returning.
pub fn build_plan(
    proof: &[Op<Digest>],
    batch: &[KeyValue],
    old_root: Option<&Digest>,
    new_root: &Digest,
) -> Result<TracePlan, PlanError> {
    // Fail fast: the stream must be accepted by the reference verifier.
    verify_consistency::<Poseidon2Hasher>(proof, old_root, new_root, batch)
        .map_err(PlanError::Rejected)?;

    // Sorted batch (verify accepted, so keys are strictly increasing).
    let mut sorted: Vec<&KeyValue> = batch.iter().collect();
    sorted.sort_by_key(|kv| kv.0);

    let perm = default_perm();
    let mut arena = Arena::default();

    let mut a_rows: Vec<ARow> = Vec::with_capacity(proof.len());
    let mut f_joins: Vec<FJoin> = Vec::new();
    let mut f_opens: Vec<FOpen> = Vec::new();
    let mut c_batch: Vec<CLeaf> = Vec::new();
    let mut c_opened: Vec<CLeaf> = Vec::new();
    let mut d_rows: Vec<DRow> = Vec::new();

    let mut r_mults = vec![0u32; R10_REAL];
    let mut p_mults = [0u32; 31];

    let mut stack: Vec<Entry> = Vec::new();
    let mut bi: u32 = 0;

    let zero_digest = [F::default(); 8];

    for (i, op) in proof.iter().enumerate() {
        let row_idx = i as u32;
        match op {
            Op::S(h) => {
                a_rows.push(ARow {
                    row_idx,
                    kind: OpKind::S,
                    old: *h,
                    new: *h,
                    old_is_none: false,
                    has_advice: false,
                    delta: 0,
                    rho: [0u32; 9],
                    batch_idx: 0,
                    node_hash_old_needed: false,
                    opened_idx: 0,
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: Some(*h),
                    new: *h,
                    advice: None,
                    row_idx,
                    subtree_start: row_idx,
                });
            }

            Op::O {
                depth,
                region,
                c_l,
                c_r,
            } => {
                let pre = node_prefix_io(&perm, *depth, region);
                let ch = node_children_io(&perm, &pre.output, c_l, c_r);
                let prefix_idx = arena.intern(pre, true); // feed-forward → children
                let children_idx = arena.intern(ch, false); // terminal (digest)
                let digest = digest_of(&ch.output);
                let opened_idx = f_opens.len() as u32;
                f_opens.push(FOpen {
                    parent_row_idx: row_idx,
                    depth: *depth,
                    region: *region,
                    c_l: *c_l,
                    c_r: *c_r,
                    prefix_idx,
                    children_idx,
                    digest,
                    mid: pre.output,
                });
                r_mults[r10_index(8, *depth as u32)] += 1; // A sends depth to R10
                a_rows.push(ARow {
                    row_idx,
                    kind: OpKind::O,
                    old: digest,
                    new: digest,
                    old_is_none: false,
                    has_advice: true,
                    delta: *depth,
                    rho: *region,
                    batch_idx: 0,
                    node_hash_old_needed: false,
                    opened_idx,
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: Some(digest),
                    new: digest,
                    advice: Some((*depth, *region)),
                    row_idx,
                    subtree_start: row_idx,
                });
            }

            Op::OL { key, value } => {
                let key_f = limbs_to_field(key);
                let value_f = value_field_limbs(value);
                let ios = leaf_perm_io(&perm, &key_f, &value_f);
                let perm_idx = [
                    arena.intern(ios[0], true),  // step 0 → step 1
                    arena.intern(ios[1], true),  // step 1 → step 2
                    arena.intern(ios[2], false), // step 2 terminal (digest)
                ];
                let digest = digest_of(&ios[2].output);
                let opened_idx = c_opened.len() as u32;
                c_opened.push(CLeaf {
                    kind: LeafKind::Opened,
                    idx: opened_idx,
                    key: key_f,
                    value: value_f,
                    digest,
                    perm_idx,
                });
                a_rows.push(ARow {
                    row_idx,
                    kind: OpKind::OL,
                    old: digest,
                    new: digest,
                    old_is_none: false,
                    has_advice: true,
                    delta: KEY_BITS,
                    rho: *key,
                    batch_idx: 0,
                    node_hash_old_needed: false,
                    opened_idx,
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: Some(digest),
                    new: digest,
                    advice: Some((KEY_BITS, *key)),
                    row_idx,
                    subtree_start: row_idx,
                });
            }

            Op::L => {
                let (k, v) = sorted[bi as usize];
                let key_f = limbs_to_field(k);
                let value_f = value_field_limbs(v);
                let ios = leaf_perm_io(&perm, &key_f, &value_f);
                let perm_idx = [
                    arena.intern(ios[0], true),  // step 0 → step 1
                    arena.intern(ios[1], true),  // step 1 → step 2
                    arena.intern(ios[2], false), // step 2 terminal (digest)
                ];
                let digest = digest_of(&ios[2].output);
                d_rows.push(DRow {
                    idx: bi,
                    key: key_f,
                    value: value_f,
                });
                c_batch.push(CLeaf {
                    kind: LeafKind::Batch,
                    idx: bi,
                    key: key_f,
                    value: value_f,
                    digest,
                    perm_idx,
                });
                a_rows.push(ARow {
                    row_idx,
                    kind: OpKind::L,
                    old: zero_digest,
                    new: digest,
                    old_is_none: true,
                    has_advice: true,
                    delta: KEY_BITS,
                    rho: *k,
                    batch_idx: bi,
                    node_hash_old_needed: false,
                    opened_idx: 0,
                    subtree_start: row_idx,
                });
                stack.push(Entry {
                    old: None,
                    new: digest,
                    advice: Some((KEY_BITS, *k)),
                    row_idx,
                    subtree_start: row_idx,
                });
                bi += 1;
            }

            Op::N { depth } => {
                let d = *depth;
                let right = stack.pop().ok_or(PlanError::Inconsistent("N underflow"))?;
                let left = stack.pop().ok_or(PlanError::Inconsistent("N underflow"))?;

                // case bits (b00/b01/b10 derived in-AIR; keep b11 for old-hash)
                let l_none = left.old.is_none();
                let r_none = right.old.is_none();
                let b11 = !l_none && !r_none;

                // R10 coherence (D13): boundary limb q, offset r_off, width w.
                let (q, r_off, w) = boundary(d);
                let k = w - r_off - 1; // L bound: L < 2^k
                let pow_b = 1u32 << k; // 2^k; pow_a = 2·pow_b derived in-AIR
                p_mults[k as usize] += 1; // Bus 7: one pow_b lookup per join

                // shared prefix H = top r_off bits of the (agreed) region limb
                let advised_rho = left
                    .advice
                    .map(|(_, r)| r)
                    .or(right.advice.map(|(_, r)| r))
                    .ok_or(PlanError::Inconsistent("N without advice"))?;
                let (h_val, _, _) = split_limb(advised_rho[q], w, r_off);
                let vr_h = variable_range(h_val, r_off);
                // k decomposition (shared across children)
                let h_k = (k / 10) as usize;
                let s_k = k % 10;
                let u_k = [h_k == 0, h_k == 1, h_k == 2];

                let mut child_coh = |adv: &Option<(u16, Key)>, side: u32| -> ChildCoh {
                    match adv {
                        Some((delta, rho)) => {
                            let (_hi, _beta, lo) = split_limb(rho[q], w, r_off);
                            let vr_l = variable_range(lo, k);
                            // R10 receives: gap (8, gap) + L digits (width_i, digit_i)
                            r_mults[r10_index(8, (delta - d - 1) as u32)] += 1;
                            for (bits, val) in vr_l.receives {
                                r_mults[r10_index(bits, val)] += 1;
                            }
                            let ld = radix1024(lo, 3);
                            ChildCoh {
                                has: true,
                                side,
                                delta: *delta,
                                rho: *rho,
                                gap: delta - d - 1,
                                l: lo,
                                l_digits: [ld[0], ld[1], ld[2]],
                            }
                        }
                        None => ChildCoh::default(),
                    }
                };
                let child_l = child_coh(&left.advice, 0);
                let child_r = child_coh(&right.advice, 1);

                // H range receives + depth
                r_mults[r10_index(8, d as u32)] += 1; // A sends depth
                for (bits, val) in vr_h.receives {
                    r_mults[r10_index(bits, val)] += 1;
                }

                let region = region_limbs(&advised_rho, d);

                // permutations: shared prefix + new children (always) + old (b11)
                let pre = node_prefix_io(&perm, d, &region);
                let prefix_idx = arena.intern(pre, true); // feed-forward → children
                let new_ch = node_children_io(&perm, &pre.output, &left.new, &right.new);
                let new_children_idx = arena.intern(new_ch, false); // terminal (digest)
                let new_digest = digest_of(&new_ch.output);

                let (old_children_idx, old_digest) = match (left.old, right.old) {
                    (None, None) => (None, None),
                    (None, Some(r)) => (None, Some(r)), // passthrough
                    (Some(l), None) => (None, Some(l)), // passthrough
                    (Some(l), Some(r)) => {
                        let old_ch = node_children_io(&perm, &pre.output, &l, &r);
                        (
                            Some(arena.intern(old_ch, false)), // terminal (digest)
                            Some(digest_of(&old_ch.output)),
                        )
                    }
                };

                let parent_row_idx = row_idx;
                // D19: subtree starts flow up from the children. Parent inherits
                // the left child's start; the left child sits at `rs − 1`.
                let ls = left.subtree_start;
                let rs = right.subtree_start;

                f_joins.push(FJoin {
                    parent_row_idx,
                    ls,
                    rs,
                    depth: d,
                    region,
                    l_old: left.old.unwrap_or(zero_digest),
                    l_new: left.new,
                    l_none,
                    r_old: right.old.unwrap_or(zero_digest),
                    r_new: right.new,
                    r_none,
                    b11,
                    q,
                    r_off,
                    w,
                    pow_b,
                    h: h_val,
                    h_digits: vr_h.digits,
                    u_r: vr_h.u,
                    s_r: vr_h.s,
                    u_k,
                    s_k,
                    child_l,
                    child_r,
                    prefix_idx,
                    new_children_idx,
                    old_children_idx,
                    old_digest,
                    new_digest,
                    mid: pre.output,
                });

                // Post-order contiguity (D19): the right child is the row
                // immediately preceding the parent, and the left child is the
                // row immediately below the right child's subtree (`rs − 1`).
                if right.row_idx + 1 != parent_row_idx {
                    return Err(PlanError::Inconsistent("post-order locality broken"));
                }
                if rs == 0 || left.row_idx + 1 != rs {
                    return Err(PlanError::Inconsistent("post-order subtree_start broken"));
                }

                a_rows.push(ARow {
                    row_idx,
                    kind: OpKind::N,
                    old: old_digest.unwrap_or(zero_digest),
                    new: new_digest,
                    old_is_none: old_digest.is_none(),
                    has_advice: true,
                    delta: d,
                    rho: region,
                    batch_idx: 0,
                    node_hash_old_needed: b11,
                    opened_idx: 0,
                    subtree_start: ls,
                });
                stack.push(Entry {
                    old: old_digest,
                    new: new_digest,
                    advice: Some((d, region)),
                    row_idx,
                    subtree_start: ls,
                });
            }
        }
    }

    if stack.len() != 1 {
        return Err(PlanError::Inconsistent("final stack not singleton"));
    }
    let root = stack.pop().unwrap();
    if root.new != *new_root || root.old.as_ref() != old_root {
        return Err(PlanError::Inconsistent("final roots disagree"));
    }

    // Canonical input range checks (D15, closes #5): every batch key/value limb
    // is proved a genuine 30/16-bit value via radix-1024 digits on the range bus.
    let limb_width = |j: usize| -> u16 { if j < 8 { 30 } else { 16 } };
    for d in &d_rows {
        for limbs in [&d.key, &d.value] {
            for (j, limb) in limbs.iter().enumerate() {
                let (_digits, receives) = canonical_limb(limb.as_canonical_u32(), limb_width(j));
                for (bits, val) in receives {
                    r_mults[r10_index(bits, val)] += 1;
                }
            }
        }
    }

    let n_b11 = f_joins.iter().filter(|j| j.b11).count();
    let publics = Publics {
        old_root: old_root.copied().unwrap_or(zero_digest),
        old_root_is_none: old_root.is_none(),
        new_root: *new_root,
    };
    let shape = Shape {
        n_ops: proof.len(),
        n_s: a_rows.iter().filter(|r| r.kind == OpKind::S).count(),
        n_open: f_opens.len(),
        n_ol: c_opened.len(),
        n_l: c_batch.len(),
        n_join: f_joins.len(),
        n_b11,
        n_batch: d_rows.len(),
        n_perms: arena.len(),
    };

    Ok(TracePlan {
        publics,
        shape,
        a_rows,
        f_joins,
        f_opens,
        c_batch,
        c_opened,
        d_rows,
        arena,
        r_mults,
        p_mults,
    })
}

// ---------------------------------------------------------------------------
// Invariant checks (DEVPLAN M2 exit criteria)
// ---------------------------------------------------------------------------

/// Assert the plan's internal consistency: pointer discipline, arena coverage,
/// and multiplicity totals equal the receiver counts they serve. Returns the
/// first violated invariant.
pub fn check_plan_invariants(plan: &TracePlan) -> Result<(), &'static str> {
    let n = plan.a_rows.len();

    // A-row indices are the identity 0..n.
    for (i, row) in plan.a_rows.iter().enumerate() {
        if row.row_idx as usize != i {
            return Err("A row_idx not identity");
        }
    }

    // Bus 1 tree-shape (D19): every non-root real row is consumed exactly once
    // as a child of some join. The right child is at `parent_row_idx − 1`; the
    // left child at `rs − 1` (rs = right child's subtree_start). Together with
    // the subtree_start chain below this proves a single contiguous post-order
    // tree — no forward edges, no disjoint cycles (README functional-graph).
    if n > 0 {
        let root_idx = n - 1;
        let mut child_count = vec![0usize; n];
        for j in &plan.f_joins {
            if j.rs == 0 || j.parent_row_idx == 0 {
                return Err("join child index underflow");
            }
            let left_idx = (j.rs - 1) as usize;
            let right_idx = (j.parent_row_idx - 1) as usize;
            if left_idx >= n || right_idx >= n {
                return Err("join child index out of range");
            }
            child_count[left_idx] += 1;
            child_count[right_idx] += 1;
        }
        for (i, c) in child_count.iter().enumerate() {
            let expect = if i == root_idx { 0 } else { 1 };
            if *c != expect {
                return Err("tree-bus child multiset imbalance");
            }
        }

        // subtree_start chain: base opcodes start at their own row; each join's
        // parent start equals its left child's start (`ls`) and its `rs`/`ls`
        // match the children's own recorded starts; the root starts at 0.
        for row in &plan.a_rows {
            let base = matches!(row.kind, OpKind::S | OpKind::O | OpKind::OL | OpKind::L);
            if base && row.subtree_start != row.row_idx {
                return Err("base opcode subtree_start ≠ row_idx");
            }
        }
        for j in &plan.f_joins {
            let left = &plan.a_rows[(j.rs - 1) as usize];
            let right = &plan.a_rows[(j.parent_row_idx - 1) as usize];
            let parent = &plan.a_rows[j.parent_row_idx as usize];
            if left.subtree_start != j.ls || right.subtree_start != j.rs {
                return Err("join child subtree_start mismatch");
            }
            if parent.subtree_start != j.ls {
                return Err("join parent subtree_start ≠ left child start");
            }
        }
        if plan.a_rows[root_idx].subtree_start != 0 {
            return Err("root subtree_start ≠ 0");
        }
    }

    // Segmented row counts match the shape.
    if plan.f_joins.len() != plan.shape.n_join
        || plan.f_opens.len() != plan.shape.n_open
        || plan.c_batch.len() != plan.shape.n_l
        || plan.c_opened.len() != plan.shape.n_ol
        || plan.d_rows.len() != plan.shape.n_batch
        || plan.arena.len() != plan.shape.n_perms
    {
        return Err("shape counts disagree with row vectors");
    }

    // Permutation budget: 3(L+OL) + 2·join + b11 + 2·open evaluations, with the
    // shared prefix realised (one prefix per junction, not per side).
    let expected_perms = 3 * (plan.shape.n_l + plan.shape.n_ol)
        + 2 * plan.shape.n_join
        + plan.shape.n_b11
        + 2 * plan.shape.n_open;
    // The arena may be *smaller* than this if any evaluations coincide, but on
    // distinct keys/positions it is exactly this count.
    if plan.arena.len() > expected_perms {
        return Err("arena larger than permutation budget");
    }

    // Arena coverage: every row's referenced permutation indices are in range,
    // and the referenced input/output actually matches the row's digest.
    let arena = plan.arena.entries();
    let check_idx = |idx: u32| -> bool { (idx as usize) < arena.len() };
    for leaf in plan.c_batch.iter().chain(plan.c_opened.iter()) {
        for &pi in &leaf.perm_idx {
            if !check_idx(pi) {
                return Err("C leaf arena index out of range");
            }
        }
        if digest_of(&arena[leaf.perm_idx[2] as usize].output) != leaf.digest {
            return Err("C leaf digest ≠ arena output");
        }
    }
    for j in &plan.f_joins {
        if !check_idx(j.prefix_idx) || !check_idx(j.new_children_idx) {
            return Err("F join arena index out of range");
        }
        if digest_of(&arena[j.new_children_idx as usize].output) != j.new_digest {
            return Err("F join new digest ≠ arena output");
        }
        // prefix sharing: old children block (b11) reuses the same prefix mid.
        if let Some(oc) = j.old_children_idx {
            if !check_idx(oc) {
                return Err("F join old arena index out of range");
            }
            let mid = arena[j.prefix_idx as usize].output;
            // old children block input = mid + old_l‖old_r
            let inp = arena[oc as usize].input;
            for k in 0..8 {
                if inp[k] != mid[k] + j.l_old[k] || inp[8 + k] != mid[8 + k] + j.r_old[k] {
                    return Err("F join old block did not reuse shared prefix");
                }
            }
        } else if j.b11 {
            return Err("b11 join missing old children block");
        }
    }
    for o in &plan.f_opens {
        if !check_idx(o.prefix_idx) || !check_idx(o.children_idx) {
            return Err("F open arena index out of range");
        }
        if digest_of(&arena[o.children_idx as usize].output) != o.digest {
            return Err("F open digest ≠ arena output");
        }
    }

    // R10 coherence reconstructs correctly (D13).
    for j in &plan.f_joins {
        let recon3 = |d: &[u32; 3]| d[0] + (d[1] << 10) + (d[2] << 20);
        if recon3(&j.h_digits) != j.h {
            return Err("coherence H digit decomposition mismatch");
        }
        // ρ[q] = 2·pow_b·H + β·pow_b + L for each advised child.
        let region_q = j.region[j.q];
        if region_q != 2 * j.pow_b * j.h {
            return Err("p[q] ≠ 2·pow_b·H");
        }
        for (ch, side) in [(&j.child_l, 0u32), (&j.child_r, 1u32)] {
            if !ch.has {
                continue;
            }
            if recon3(&ch.l_digits) != ch.l {
                return Err("coherence L digit decomposition mismatch");
            }
            let rho_q = ch.rho[j.q];
            if rho_q != 2 * j.pow_b * j.h + side * j.pow_b + ch.l {
                return Err("ρ[q] ≠ 2·pow_b·H + β·pow_b + L");
            }
        }
    }

    // Multiplicity totals equal the receiver counts they serve.
    //   R (range bus): one depth per N and O row, plus per advised child the gap
    //   and 3 L digits, plus 3 H digits per join. Each is one Table-R receive.
    let advised_children: u32 = plan
        .f_joins
        .iter()
        .map(|j| j.child_l.has as u32 + j.child_r.has as u32)
        .sum();
    let r_total: u32 = plan.r_mults.iter().sum();
    let r_expected = plan.shape.n_join as u32   // N depths
        + plan.shape.n_open as u32              // O depths
        + 3 * plan.shape.n_join as u32          // H digits
        + 4 * advised_children                  // gap + 3 L digits per advised child
        + 52 * plan.shape.n_batch as u32; // canonical key/value digits (26 each)
    if r_total != r_expected {
        return Err("R multiplicity total ≠ depths + H/L digits + gaps + input digits");
    }
    //   P (Bus 7): one pow_b per join row.
    let p_total: u32 = plan.p_mults.iter().sum();
    if p_total != plan.shape.n_join as u32 {
        return Err("P multiplicity total ≠ joins");
    }

    // Every join has ≥ 1 advised child, and a new junction has both advised.
    for j in &plan.f_joins {
        if !j.child_l.has && !j.child_r.has {
            return Err("join with no advised child");
        }
        if !j.b11 && (!j.child_l.has || !j.child_r.has) {
            return Err("new junction without both children advised");
        }
    }

    Ok(())
}
