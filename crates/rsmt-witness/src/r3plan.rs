//! R3 row-plan structs (M3), built without reusing legacy `ARow/CLeaf/DRow`
//! fields by position. This module currently holds the **fused leaf** plan
//! (`R3Leaf`), which replaces both Table C (leaf sponge) and Table D (batch /
//! canonical input digits) with one row per `L`/`O_l` (`DEVPLAN-R3.md` §5.3):
//!
//! ```text
//! a_row_idx, key_digits[26], value_digits[26], mid_0[16], mid_1[16], digest[8]
//! ```
//!
//! The nine key and value limbs are *linear expressions* in the 26 radix-1024
//! digits, not stored columns; each digit is range-checked at its fixed width
//! against Table R. The three leaf-sponge permutations are recorded as
//! occurrences in the [`PermutationPlan`] (2 feed-forward + 1 terminal).

use p3_baby_bear::Poseidon2BabyBear;
use p3_field::PrimeCharacteristicRing;
use rsmt_core::{Key, LIMBS, Value32, limb_start, limb_width, region_limbs, split_limb};
use rsmt_hash::{
    Digest, STATE_WIDTH, State, digest_of, leaf_perm_io, limbs_to_field, node_children_io,
    node_prefix_io,
};

use crate::r3arena::{JoinPermIdx, LeafPermIdx, OpenPermIdx, PermutationPlan};
use crate::r10::{canonical_limb, n_digits, radix1024, variable_range};

/// Number of radix-1024 digits for a canonical 256-bit key or value
/// (`8×3 + 1×2`).
pub const N_LEAF_DIGITS: usize = 26;

const _: () = assert!(N_LEAF_DIGITS == 26);

/// One fused leaf row (an `L` or `O_l`). Digits are little-endian radix-1024;
/// mids and digest are the recorded Poseidon2 outputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R3Leaf {
    /// The Table-A row index this leaf binds to on the leaf bus.
    pub a_row_idx: u32,
    pub key_digits: [u32; N_LEAF_DIGITS],
    pub value_digits: [u32; N_LEAF_DIGITS],
    pub mid_0: State,
    pub mid_1: State,
    pub digest: Digest,
    /// Occurrence indices of the three leaf permutations in the arena.
    pub perm: LeafPermIdx,
}

/// Reconstruct the nine limbs from 26 radix-1024 digits (`limb_j = Σ dᵢ·1024ⁱ`).
/// The inverse of the digit decomposition; injective because each digit is
/// range-checked below its fixed width.
pub fn reconstruct_limbs(digits: &[u32; N_LEAF_DIGITS]) -> Key {
    let mut limbs = [0u32; LIMBS];
    let mut idx = 0;
    for (j, limb) in limbs.iter_mut().enumerate() {
        let n = n_digits(limb_width(j));
        let mut acc = 0u32;
        for i in 0..n {
            acc += digits[idx + i] << (10 * i as u32);
        }
        *limb = acc;
        idx += n;
    }
    limbs
}

/// Build one fused leaf row, recording its three permutations as occurrences in
/// `plan` (no dedup). Returns the row plus the 52 Table-R range receives
/// `(width, digit)` that prove every digit canonical.
pub fn build_leaf(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    plan: &mut PermutationPlan,
    a_row_idx: u32,
    key: &Key,
    value: &Value32,
) -> (R3Leaf, Vec<(u32, u32)>) {
    let value_limbs = value.limbs();
    let mut key_digits = [0u32; N_LEAF_DIGITS];
    let mut value_digits = [0u32; N_LEAF_DIGITS];
    let mut receives = Vec::with_capacity(2 * N_LEAF_DIGITS);
    let mut idx = 0;
    for j in 0..LIMBS {
        let w = limb_width(j);
        let (kd, kr) = canonical_limb(key[j], w);
        let (vd, vr) = canonical_limb(value_limbs[j], w);
        key_digits[idx..idx + kd.len()].copy_from_slice(&kd);
        value_digits[idx..idx + vd.len()].copy_from_slice(&vd);
        receives.extend(kr);
        receives.extend(vr);
        idx += kd.len();
    }

    let key_f = limbs_to_field(key);
    let value_f = limbs_to_field(&value_limbs);
    let ios = leaf_perm_io(perm, &key_f, &value_f);
    let perm_idx = plan.record_leaf(ios);

    let leaf = R3Leaf {
        a_row_idx,
        key_digits,
        value_digits,
        mid_0: ios[0].output,
        mid_1: ios[1].output,
        digest: digest_of(&ios[2].output),
        perm: perm_idx,
    };
    (leaf, receives)
}

// ---------------------------------------------------------------------------
// Canonical opened junction (Table O, §5.5)
// ---------------------------------------------------------------------------

/// Locate absolute depth `d < 256` in the limb array: returns
/// `(q, r_off, width)` where `q` is the limb containing bit `d`, `r_off = d −
/// limb_start(q)` the intra-limb offset, and `width` the limb's bit width.
pub fn locate_depth(d: u16) -> (usize, u16, u16) {
    debug_assert!(d < 256);
    if d < 240 {
        let q = (d / 30) as usize;
        (q, d - limb_start(q), 30)
    } else {
        (8, d - 240, 16)
    }
}

/// One canonical opened-junction row (an `O`). The region is a genuine
/// left-aligned `depth`-bit prefix: limbs above the boundary are full canonical
/// limbs, the boundary limb keeps its top `r_off` bits (`= 2·pow_b·H`), and
/// limbs below are zero (`DEVPLAN-R3.md` §5.5, soundness lemma S5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R3Open {
    pub a_row_idx: u32,
    pub depth: u16,
    pub region_digits: [u32; N_LEAF_DIGITS],
    /// Boundary limb index (`0..9`); one-hot in the AIR.
    pub q: usize,
    /// Intra-limb offset `r_off = depth − limb_start(q)` (bits kept in limb `q`).
    pub r_off: u16,
    /// `pow_b = 2^(W(q) − r_off − 1)`; the boundary limb is `2·pow_b·H`.
    pub pow_b: u32,
    /// The `r_off`-bit prefix value held in the boundary limb.
    pub h: u32,
    pub h_digits: [u32; 3],
    pub h_u: [bool; 3],
    pub prefix_mid: State,
    pub left_digest: Digest,
    pub right_digest: Digest,
    pub digest: Digest,
    pub perm: OpenPermIdx,
}

/// Build one canonical opened-junction row, recording the node prefix
/// (feed-forward) and node children block (terminal) as arena occurrences.
/// Returns the row plus the Table-R range receives: 26 canonical region digits
/// plus the 3 variable-width `H` digits.
pub fn build_open(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    plan: &mut PermutationPlan,
    a_row_idx: u32,
    depth: u16,
    region: &Key,
    left: &Digest,
    right: &Digest,
) -> (R3Open, Vec<(u32, u32)>) {
    let (q, r_off, w) = locate_depth(depth);

    // Canonical digits of every region limb (each proved `< 2^width`).
    let mut region_digits = [0u32; N_LEAF_DIGITS];
    let mut receives = Vec::with_capacity(N_LEAF_DIGITS + 3);
    let mut idx = 0;
    for (j, &limb) in region.iter().enumerate() {
        let (d, r) = canonical_limb(limb, limb_width(j));
        region_digits[idx..idx + d.len()].copy_from_slice(&d);
        receives.extend(r);
        idx += d.len();
    }

    // Boundary limb = 2·pow_b·H, with H the top r_off bits (H = 0 when r_off = 0).
    let shift = w - r_off; // bits below the kept prefix in the boundary limb
    let h = if r_off == 0 { 0 } else { region[q] >> shift };
    debug_assert_eq!(region[q], h << shift, "boundary limb is not 2^(W−r)·H");
    let pow_b = 1u32 << (w - r_off - 1);
    let vr = variable_range(h, r_off);

    // Node hash: shared prefix (feed-forward) then children block (terminal).
    let prefix = node_prefix_io(perm, depth, region);
    let node = node_children_io(perm, &prefix.output, left, right);
    let perm_idx = plan.record_open(prefix, node);
    receives.extend(vr.receives);

    let open = R3Open {
        a_row_idx,
        depth,
        region_digits,
        q,
        r_off,
        pow_b,
        h,
        h_digits: vr.digits,
        h_u: vr.u,
        prefix_mid: prefix.output,
        left_digest: *left,
        right_digest: *right,
        digest: digest_of(&node.output),
        perm: perm_idx,
    };
    (open, receives)
}

// ---------------------------------------------------------------------------
// Join coherence (Table J, §5.4)
// ---------------------------------------------------------------------------

/// Coherence data for one advised child of a junction (side 0 = left, 1 = right).
/// The child's boundary limb satisfies `rho[q] = region[q] + side·pow_b + L`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ChildCoh {
    pub has: bool,
    pub side: u32,
    pub delta: u16,
    pub rho: Key,
    /// `gap = delta − depth − 1` (an 8-bit range check).
    pub gap: u16,
    /// Child-only tail `L = low (W − r_off − 1) bits of rho[q]`.
    pub l: u32,
    pub l_digits: [u32; 3],
}

/// A junction's two children as consumed from the stack (post-order).
#[derive(Clone, Copy, Debug)]
pub struct JoinChild {
    pub old: Option<Digest>,
    pub new: Digest,
    pub advice: Option<(u16, Key)>,
    pub subtree_start: u32,
    pub row_idx: u32,
}

/// One join (`N`) row: coherence decomposition, four-way old state, and the node
/// hash. Ports the reference join logic (`plan.rs` N-handler) to the
/// occurrence arena and drops the union-with-openings tax (`DEVPLAN-R3.md` §5.4).
#[derive(Clone, Debug)]
pub struct R3Join {
    pub parent_row_idx: u32,
    pub ls: u32,
    pub rs: u32,
    pub depth: u16,
    pub region: Key,
    pub q: usize,
    pub r_off: u16,
    pub w: u16,
    pub pow_b: u32,
    pub h: u32,
    pub h_digits: [u32; 3],
    pub u_r: [bool; 3],
    pub s_r: u16,
    pub u_k: [bool; 3],
    pub s_k: u16,
    pub child_l: ChildCoh,
    pub child_r: ChildCoh,
    pub l_old: Digest,
    pub l_new: Digest,
    pub l_none: bool,
    pub r_old: Digest,
    pub r_new: Digest,
    pub r_none: bool,
    pub b11: bool,
    pub parent_none: bool,
    pub parent_old: Digest,
    pub parent_new: Digest,
    pub mid: State,
    pub new_digest: Digest,
    pub old_digest: Option<Digest>,
    pub perm: JoinPermIdx,
}

/// Build one join row. Returns the row plus the Table-R range receives
/// `(bits, value)` (depth, `H` digits, and per advised child the gap byte + `L`
/// digits) and the pow2 exponent `k = W − r_off − 1` for `pow_b`.
pub fn build_join(
    perm: &Poseidon2BabyBear<STATE_WIDTH>,
    plan: &mut PermutationPlan,
    parent_row_idx: u32,
    depth: u16,
    left: &JoinChild,
    right: &JoinChild,
) -> (R3Join, Vec<(u32, u32)>, u32) {
    let d = depth;
    let (q, r_off, w) = locate_depth(d);
    let k = w - r_off - 1;
    let pow_b = 1u32 << k;

    let advised_rho = left
        .advice
        .map(|(_, r)| r)
        .or(right.advice.map(|(_, r)| r))
        .expect("N without advice");
    let (h_val, _, _) = split_limb(advised_rho[q], w, r_off);
    let vr_h = variable_range(h_val, r_off);
    let h_k = (k / 10) as usize;
    let s_k = k % 10;
    let u_k = [h_k == 0, h_k == 1, h_k == 2];

    let mut receives: Vec<(u32, u32)> = Vec::new();
    receives.push((8, d as u32)); // depth (A sends it too)
    receives.extend(vr_h.receives);

    let mut child_coh = |adv: &Option<(u16, Key)>, side: u32| -> ChildCoh {
        match adv {
            Some((delta, rho)) => {
                let (_hi, _beta, lo) = split_limb(rho[q], w, r_off);
                let vr_l = variable_range(lo, k);
                receives.push((8, (delta - d - 1) as u32)); // gap byte
                receives.extend(vr_l.receives);
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

    let region = region_limbs(&advised_rho, d);
    let l_none = left.old.is_none();
    let r_none = right.old.is_none();
    let b11 = !l_none && !r_none;

    // Permutations: shared prefix (ff), new children (term), old children (term iff b11).
    let pre = node_prefix_io(perm, d, &region);
    let new_ch = node_children_io(perm, &pre.output, &left.new, &right.new);
    let new_digest = digest_of(&new_ch.output);

    let (old_children_io, old_digest) = match (left.old, right.old) {
        (None, None) => (None, None),
        (None, Some(r)) => (None, Some(r)), // passthrough
        (Some(l), None) => (None, Some(l)), // passthrough
        (Some(l), Some(r)) => {
            let old_ch = node_children_io(perm, &pre.output, &l, &r);
            (Some(old_ch), Some(digest_of(&old_ch.output)))
        }
    };
    let perm_idx = plan.record_join(pre, new_ch, old_children_io);

    let zero = [p3_baby_bear::BabyBear::ZERO; 8];
    let join = R3Join {
        parent_row_idx,
        ls: left.subtree_start,
        rs: right.subtree_start,
        depth: d,
        region,
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
        l_old: left.old.unwrap_or(zero),
        l_new: left.new,
        l_none,
        r_old: right.old.unwrap_or(zero),
        r_new: right.new,
        r_none,
        b11,
        parent_none: old_digest.is_none(),
        parent_old: old_digest.unwrap_or(zero),
        parent_new: new_digest,
        mid: pre.output,
        new_digest,
        old_digest,
        perm: perm_idx,
    };
    (join, receives, k as u32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use rsmt_core::{Hasher, bytes_to_limbs, is_canonical_region};
    use rsmt_hash::{DOMAIN_LEAF, Poseidon2Hasher, RATE, default_perm};

    fn rand_leaf(seed: u8) -> (Key, Value32) {
        let mut kb = [0u8; 32];
        let mut vb = [0u8; 32];
        for i in 0..32 {
            kb[i] = seed.wrapping_add(i as u8).wrapping_mul(37);
            vb[i] = seed.wrapping_add(i as u8).wrapping_mul(101).wrapping_add(7);
        }
        (bytes_to_limbs(&kb), Value32::new(vb))
    }

    #[test]
    fn digits_reconstruct_key_and_value_exactly() {
        let perm = default_perm();
        for seed in 0..16u8 {
            let (key, value) = rand_leaf(seed);
            let mut plan = PermutationPlan::new();
            let (leaf, receives) = build_leaf(&perm, &mut plan, 0, &key, &value);
            assert_eq!(reconstruct_limbs(&leaf.key_digits), key);
            assert_eq!(reconstruct_limbs(&leaf.value_digits), value.limbs());
            // Every range receive is a valid R10 entry (digit < 2^width).
            assert_eq!(receives.len(), 52);
            for (w, d) in receives {
                assert!(d < (1u32 << w), "digit {d} ≥ 2^{w}");
            }
        }
    }

    #[test]
    fn digest_matches_reference_leaf_hash() {
        let perm = default_perm();
        for seed in 0..16u8 {
            let (key, value) = rand_leaf(seed);
            let mut plan = PermutationPlan::new();
            let (leaf, _) = build_leaf(&perm, &mut plan, 5, &key, &value);
            assert_eq!(leaf.digest, Poseidon2Hasher::hash_leaf(&key, &value));
        }
    }

    #[test]
    fn sponge_input_expressions_match_arena() {
        // The AIR reconstructs each sponge step's input from the digit-derived
        // limbs and the previous mid; assert those exact expressions equal the
        // arena's recorded permutation inputs, so the L AIR's bus tuples are
        // faithful.
        let perm = default_perm();
        let (key, value) = rand_leaf(3);
        let mut plan = PermutationPlan::new();
        let (leaf, _) = build_leaf(&perm, &mut plan, 0, &key, &value);
        let key_f = limbs_to_field(&key);
        let value_f = limbs_to_field(&value.limbs());
        let ff = plan.feed_forward();
        let term = plan.terminal();
        let io0 = ff[leaf.perm.ff0 as usize];
        let io1 = ff[leaf.perm.ff1 as usize];
        let io2 = term[leaf.perm.term as usize];

        // Step 0 input: [DOMAIN_LEAF, key[0..7], 0×8].
        let mut in0 = [p3_baby_bear::BabyBear::ZERO; STATE_WIDTH];
        in0[0] = p3_baby_bear::BabyBear::from_u32(DOMAIN_LEAF);
        in0[1..RATE].copy_from_slice(&key_f[..RATE - 1]);
        assert_eq!(io0.input, in0);
        assert_eq!(io0.output, leaf.mid_0);

        // Step 1 input: mid_0 + [key7, key8, value0..5, 0×8].
        let mut in1 = leaf.mid_0;
        in1[0] += key_f[7];
        in1[1] += key_f[8];
        for i in 0..6 {
            in1[2 + i] += value_f[i];
        }
        assert_eq!(io1.input, in1);
        assert_eq!(io1.output, leaf.mid_1);

        // Step 2 input: mid_1 + [value6, value7, value8, 0×13].
        let mut in2 = leaf.mid_1;
        in2[0] += value_f[6];
        in2[1] += value_f[7];
        in2[2] += value_f[8];
        assert_eq!(io2.input, in2);
        assert_eq!(&io2.output[..8], &leaf.digest[..]);
    }

    #[test]
    fn two_leaves_record_three_perms_each() {
        let perm = default_perm();
        let mut plan = PermutationPlan::new();
        let (k0, v0) = rand_leaf(1);
        let (k1, v1) = rand_leaf(2);
        build_leaf(&perm, &mut plan, 0, &k0, &v0);
        build_leaf(&perm, &mut plan, 1, &k1, &v1);
        // 2 leaves → 4 feed-forward (2 each) + 2 terminal (1 each).
        plan.verify_counts(2, 0, 0, 0).expect("two-leaf counts");
        assert_eq!(plan.n_ff(), 4);
        assert_eq!(plan.n_term(), 2);
    }

    // -- Table O (canonical opened junction, S5) ----------------------------

    fn digest_of_u32(seed: u32) -> Digest {
        core::array::from_fn(|i| p3_baby_bear::BabyBear::from_u32(seed.wrapping_add(i as u32)))
    }

    /// Exhaustive over all 256 depths: the opening's region reconstructs to a
    /// canonical `depth`-bit prefix and every boundary equation holds. This is
    /// soundness lemma S5 at the witness layer (finding §4: openings were never
    /// range-checked).
    #[test]
    fn open_region_is_canonical_for_every_depth() {
        let perm = default_perm();
        // A full random 256-bit "key"; its depth-d prefix is the region.
        let full = bytes_to_limbs(&core::array::from_fn(|i| {
            (i as u8).wrapping_mul(53).wrapping_add(9)
        }));
        for depth in 0u16..256 {
            let region = region_limbs(&full, depth);
            let mut plan = PermutationPlan::new();
            let (o, receives) = build_open(
                &perm,
                &mut plan,
                depth as u32,
                depth,
                &region,
                &digest_of_u32(1),
                &digest_of_u32(2),
            );

            // Region reconstructs exactly, and is canonical for this depth.
            assert_eq!(reconstruct_limbs(&o.region_digits), region, "depth {depth}");
            assert!(is_canonical_region(&region, depth));

            // Boundary structure.
            let (q, r_off, w) = locate_depth(depth);
            assert_eq!(o.q, q);
            assert_eq!(o.r_off, r_off);
            assert_eq!(depth, limb_start(q) + r_off);
            assert!(o.h < (1u32 << r_off) || r_off == 0 && o.h == 0);
            // region[q] = 2·pow_b·H
            assert_eq!(region[q], 2 * o.pow_b * o.h, "depth {depth} boundary limb");
            // pow_b = 2^(W − r_off − 1)
            assert_eq!(o.pow_b, 1u32 << (w - r_off - 1));
            // limbs strictly above the boundary are zero
            for (j, &limb) in region.iter().enumerate() {
                if j > q {
                    assert_eq!(limb, 0, "depth {depth} limb {j} not zero below boundary");
                }
            }
            // Every range receive is a valid R10 entry.
            for (bits, d) in receives {
                assert!(d < (1u32 << bits), "digit {d} ≥ 2^{bits} (depth {depth})");
            }
        }
    }

    #[test]
    fn open_edge_depths_0_239_240_255() {
        let perm = default_perm();
        let full = bytes_to_limbs(&[0xFFu8; 32]);
        for depth in [0u16, 239, 240, 255] {
            let region = region_limbs(&full, depth);
            let mut plan = PermutationPlan::new();
            let (o, _) = build_open(
                &perm,
                &mut plan,
                0,
                depth,
                &region,
                &digest_of_u32(3),
                &digest_of_u32(4),
            );
            assert_eq!(reconstruct_limbs(&o.region_digits), region);
            if depth == 0 {
                // depth 0 forces the all-zero region.
                assert_eq!(region, [0u32; 9]);
            }
        }
    }

    #[test]
    fn open_digest_matches_reference_node_hash() {
        let perm = default_perm();
        let full = bytes_to_limbs(&[0xABu8; 32]);
        let (l, r) = (digest_of_u32(10), digest_of_u32(20));
        for depth in [1u16, 7, 100, 200, 255] {
            let region = region_limbs(&full, depth);
            let mut plan = PermutationPlan::new();
            let (o, _) = build_open(&perm, &mut plan, 0, depth, &region, &l, &r);
            assert_eq!(o.digest, Poseidon2Hasher::hash_node(depth, &region, &l, &r));
            // one prefix (ff) + one node (term) recorded
            plan.verify_counts(0, 0, 1, 0).expect("one-open counts");
        }
    }

    // -- Table J (join coherence, S6/S7) ------------------------------------

    /// Two leaf keys diverging exactly at `depth`: left has bit `depth` = 0,
    /// right = 1, sharing the `depth`-bit prefix of `base`.
    fn diverging_keys(base: &Key, depth: u16) -> (Key, Key) {
        use rsmt_core::{key_bit, limbs_to_bytes};
        let prefix = region_limbs(base, depth);
        let mut lb = limbs_to_bytes(&prefix);
        let mut rb = lb;
        // set some distinguishing low bits below depth so the leaves are full keys
        lb[31] |= 0x01;
        rb[31] |= 0x05;
        // force bit `depth`: left 0, right 1
        let set_bit = |bytes: &mut [u8; 32], d: u16, v: u32| {
            let (byte, bit) = ((d / 8) as usize, 7 - (d % 8));
            if v == 1 {
                bytes[byte] |= 1 << bit;
            } else {
                bytes[byte] &= !(1 << bit);
            }
        };
        set_bit(&mut lb, depth, 0);
        set_bit(&mut rb, depth, 1);
        let (lk, rk) = (bytes_to_limbs(&lb), bytes_to_limbs(&rb));
        debug_assert_eq!(key_bit(&lk, depth), 0);
        debug_assert_eq!(key_bit(&rk, depth), 1);
        (lk, rk)
    }

    fn genesis_join(depth: u16) -> (R3Join, PermutationPlan, Key, Key, Digest, Digest) {
        let perm = default_perm();
        let base = bytes_to_limbs(&[0x6Cu8; 32]);
        let (lk, rk) = diverging_keys(&base, depth);
        let lv = Value32::new([1u8; 32]);
        let rv = Value32::new([2u8; 32]);
        let l_new = Poseidon2Hasher::hash_leaf(&lk, &lv);
        let r_new = Poseidon2Hasher::hash_leaf(&rk, &rv);
        let mut plan = PermutationPlan::new();
        let left = JoinChild {
            old: None,
            new: l_new,
            advice: Some((256, lk)),
            subtree_start: 0,
            row_idx: 0,
        };
        let right = JoinChild {
            old: None,
            new: r_new,
            advice: Some((256, rk)),
            subtree_start: 1,
            row_idx: 1,
        };
        let (j, _, _) = build_join(&perm, &mut plan, 2, depth, &left, &right);
        (j, plan, lk, rk, l_new, r_new)
    }

    #[test]
    fn join_coherence_reconstructs_child_boundary_limbs() {
        // rho[q] = region[q] + side·pow_b + L for each advised child (S6).
        for depth in [1u16, 5, 29, 30, 100, 200, 239, 240, 255] {
            let (j, _, lk, rk, _, _) = genesis_join(depth);
            let q = j.q;
            // parent region is the depth-prefix; child boundary equations hold.
            assert_eq!(lk[q], j.region[q] + j.child_l.side * j.pow_b + j.child_l.l);
            assert_eq!(rk[q], j.region[q] + j.child_r.side * j.pow_b + j.child_r.l);
            assert_eq!(j.child_l.side, 0);
            assert_eq!(j.child_r.side, 1);
            // region is canonical for depth and equals both children's prefix.
            assert!(is_canonical_region(&j.region, depth));
            assert_eq!(region_limbs(&lk, depth), j.region);
            assert_eq!(region_limbs(&rk, depth), j.region);
        }
    }

    #[test]
    fn join_new_digest_matches_reference() {
        for depth in [1u16, 100, 255] {
            let (j, mut plan, _, _, l_new, r_new) = genesis_join(depth);
            assert_eq!(
                j.new_digest,
                Poseidon2Hasher::hash_node(depth, &j.region, &l_new, &r_new)
            );
            // genesis join: both children new (old None) → b00, no old block.
            assert!(!j.b11);
            assert!(j.parent_none);
            assert_eq!(j.old_digest, None);
            // 1 feed-forward prefix + 1 terminal new-children block.
            plan.verify_counts(0, 1, 0, 0).expect("b00 join counts");
            assert_eq!(plan.n_ff(), 1);
            assert_eq!(plan.n_term(), 1);
            let _ = &mut plan;
        }
    }

    #[test]
    fn join_four_way_old_state() {
        let perm = default_perm();
        let base = bytes_to_limbs(&[0x33u8; 32]);
        let depth = 40u16;
        let (lk, rk) = diverging_keys(&base, depth);
        let l_old = digest_of_u32(50);
        let r_old = digest_of_u32(60);
        let l_new = digest_of_u32(70);
        let r_new = digest_of_u32(80);

        // b11: both children present → old digest = hash_node(old_l, old_r).
        let mut plan = PermutationPlan::new();
        let left = JoinChild {
            old: Some(l_old),
            new: l_new,
            advice: Some((256, lk)),
            subtree_start: 0,
            row_idx: 0,
        };
        let right = JoinChild {
            old: Some(r_old),
            new: r_new,
            advice: Some((256, rk)),
            subtree_start: 1,
            row_idx: 1,
        };
        let (j, _, _) = build_join(&perm, &mut plan, 2, depth, &left, &right);
        assert!(j.b11);
        assert_eq!(
            j.old_digest,
            Some(Poseidon2Hasher::hash_node(depth, &j.region, &l_old, &r_old))
        );
        plan.verify_counts(0, 1, 0, 1).expect("b11 counts"); // prefix + new + old
        assert_eq!(plan.n_term(), 2);

        // b10: left present, right new → passthrough left old.
        let mut plan = PermutationPlan::new();
        let left = JoinChild {
            old: Some(l_old),
            new: l_new,
            advice: Some((256, lk)),
            subtree_start: 0,
            row_idx: 0,
        };
        let right = JoinChild {
            old: None,
            new: r_new,
            advice: Some((256, rk)),
            subtree_start: 1,
            row_idx: 1,
        };
        let (j, _, _) = build_join(&perm, &mut plan, 2, depth, &left, &right);
        assert!(!j.b11);
        assert_eq!(j.old_digest, Some(l_old)); // passthrough
        plan.verify_counts(0, 1, 0, 0).expect("b10 counts");
    }
}
