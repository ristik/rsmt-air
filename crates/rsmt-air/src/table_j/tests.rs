//! Table J: the coherence/four-way local constraints (the S6/S7 arithmetization)
//! validated against real `build_join` output, per-family negatives, and a
//! degree regression. Full cross-table bus balance is the M7 end-to-end test.

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

use rsmt_core::{Hasher, Key, bytes_to_limbs, key_bit, limbs_to_bytes, region_limbs};
use rsmt_hash::{Digest, Poseidon2Hasher, default_perm};
use rsmt_witness::r3arena::PermutationPlan;
use rsmt_witness::r3plan::{JoinChild, R3Join, build_join};

use super::*;

fn diverging_keys(base: &Key, depth: u16) -> (Key, Key) {
    let prefix = region_limbs(base, depth);
    let mut lb = limbs_to_bytes(&prefix);
    let mut rb = lb;
    lb[31] |= 0x01;
    rb[31] |= 0x05;
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

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|i| BabyBear::from_u32(seed.wrapping_add(i as u32)))
}

/// A genesis join (both children new leaves) at `depth`, row indices 0/1/2.
fn genesis_join(depth: u16, seed: u8) -> R3Join {
    let perm = default_perm();
    let base = bytes_to_limbs(&[seed; 32]);
    let (lk, rk) = diverging_keys(&base, depth);
    let l_new = Poseidon2Hasher::hash_leaf(&lk, &rsmt_core::Value32::new([1u8; 32]));
    let r_new = Poseidon2Hasher::hash_leaf(&rk, &rsmt_core::Value32::new([2u8; 32]));
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
    build_join(&perm, &mut plan, 2, depth, &left, &right).0
}

/// A b11 join (both children have old state).
fn b11_join(depth: u16) -> R3Join {
    let perm = default_perm();
    let base = bytes_to_limbs(&[0x99u8; 32]);
    let (lk, rk) = diverging_keys(&base, depth);
    let mut plan = PermutationPlan::new();
    let left = JoinChild {
        old: Some(digest(11)),
        new: digest(21),
        advice: Some((256, lk)),
        subtree_start: 0,
        row_idx: 0,
    };
    let right = JoinChild {
        old: Some(digest(31)),
        new: digest(41),
        advice: Some((256, rk)),
        subtree_start: 1,
        row_idx: 1,
    };
    build_join(&perm, &mut plan, 2, depth, &left, &right).0
}

#[test]
fn width_is_142() {
    assert_eq!(TABLE_J_WIDTH, 142);
    assert_eq!(TABLE_J_PREP_WIDTH, 1);
}

#[test]
fn constraints_pass_on_real_joins() {
    // Depths across every limb boundary plus a b11 junction.
    let mut joins: Vec<R3Join> = (0u16..256)
        .step_by(11)
        .filter(|&d| d != 0) // depth 0 has no coherence prefix bits to check meaningfully
        .map(|d| genesis_join(d, 0x6C))
        .collect();
    joins.push(b11_join(40));
    joins.push(b11_join(200));
    let (trace, real, height) = build_trace(&joins);
    let air = TableJAir::new(height, real);
    check_constraints(&air, &trace, &[]);
    assert_eq!(real, joins.len());
}

fn expect_violation(
    air: &TableJAir,
    trace: &RowMajorMatrix<BabyBear>,
    mutate: impl FnOnce(&mut Vec<BabyBear>),
) {
    let mut bad = trace.values.clone();
    mutate(&mut bad);
    let bad_trace = RowMajorMatrix::new(bad, TABLE_J_WIDTH);
    let air = air.clone();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &[]);
    }));
    assert!(r.is_err(), "expected a constraint violation");
}

#[test]
fn negatives_one_per_family() {
    let joins = vec![genesis_join(100, 0x6C), b11_join(40)];
    let (trace, real, height) = build_trace(&joins);
    let air = TableJAir::new(height, real);
    check_constraints(&air, &trace, &[]); // baseline passes
    let w = TABLE_J_WIDTH;

    // Offsets (match JCols / the CI_* constants).
    const CI_DEPTH: usize = 3;
    const CI_H: usize = 24;
    const CI_L_L: usize = 64; // left child tail L
    const CI_B11: usize = 102;
    const CI_PARENT_OLD: usize = 104;

    // depth relation: bump depth on row 0.
    expect_violation(&air, &trace, |v| v[CI_DEPTH] += BabyBear::ONE);

    // coherence H: bump the shared prefix H (region_q ≠ 2·pow_b·H).
    expect_violation(&air, &trace, |v| v[CI_H] += BabyBear::ONE);

    // child tail: bump left L (ρ_l[q] ≠ p[q] + L_l).
    expect_violation(&air, &trace, |v| v[CI_L_L] += BabyBear::ONE);

    // four-way: on the b11 row (row 1), corrupt an old-children digest slot so
    // b11 ⇒ parent_old must equal the hashed old block (bound via bus, but the
    // b00/b10 local rules still constrain parent_old here — use row 0, b00:
    // parent_none ⇒ parent_old = 0).
    expect_violation(&air, &trace, |v| v[CI_PARENT_OLD] = BabyBear::ONE);

    // case bit: flip b11 on row 0 (genesis is b00, b11 must be 0).
    expect_violation(&air, &trace, |v| v[CI_B11] = BabyBear::ONE);

    // padding hygiene.
    if height > real {
        expect_violation(&air, &trace, |v| v[real * w] = BabyBear::ONE);
    }
}

#[test]
fn degree_is_at_most_three() {
    use p3_air::{AirLayout, get_max_constraint_degree};
    let air = TableJAir::new(8, 2);
    let layout = AirLayout {
        main_width: TABLE_J_WIDTH,
        preprocessed_width: TABLE_J_PREP_WIDTH,
        num_public_values: 0,
        ..Default::default()
    };
    let deg = get_max_constraint_degree::<BabyBear, _>(&air, layout);
    assert!(deg <= 3, "J local degree {deg} exceeds 3");
}
