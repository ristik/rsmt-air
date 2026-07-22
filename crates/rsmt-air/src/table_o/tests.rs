//! Table O: local boundary constraints (the S5 arithmetization) over real
//! openings across many depths, per-family negatives, and a degree regression.
//! Full bus balance (range/pow2/p2ff/p2term/parent) is the M7 end-to-end test.

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

use rsmt_core::{bytes_to_limbs, region_limbs};
use rsmt_hash::{Digest, default_perm};
use rsmt_witness::r3arena::PermutationPlan;
use rsmt_witness::r3plan::{R3Open, build_open};

use super::*;

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|i| BabyBear::from_u32(seed.wrapping_add(i as u32)))
}

fn opens(depths: &[u16]) -> Vec<R3Open> {
    let perm = default_perm();
    let mut plan = PermutationPlan::new();
    let full = bytes_to_limbs(&core::array::from_fn(|i| {
        (i as u8).wrapping_mul(53).wrapping_add(9)
    }));
    depths
        .iter()
        .enumerate()
        .map(|(i, &d)| {
            let region = region_limbs(&full, d);
            build_open(
                &perm,
                &mut plan,
                i as u32,
                d,
                &region,
                &digest(1),
                &digest(2),
            )
            .0
        })
        .collect()
}

#[test]
fn width_is_89() {
    assert_eq!(TABLE_O_WIDTH, 89);
    assert_eq!(TABLE_O_PREP_WIDTH, 1);
}

#[test]
fn constraints_pass_over_many_depths() {
    // Cover every limb boundary plus interior and edge depths.
    let depths: Vec<u16> = (0u16..256)
        .step_by(7)
        .chain([0, 1, 29, 30, 239, 240, 255])
        .collect();
    let os = opens(&depths);
    let (trace, real, height) = build_trace(&os);
    let air = TableOAir::new(height, real);
    check_constraints(&air, &trace, &[]);
    assert_eq!(real, depths.len());
}

fn expect_violation(
    air: &TableOAir,
    trace: &RowMajorMatrix<BabyBear>,
    mutate: impl FnOnce(&mut Vec<BabyBear>),
) {
    let mut bad = trace.values.clone();
    mutate(&mut bad);
    let bad_trace = RowMajorMatrix::new(bad, TABLE_O_WIDTH);
    let air = air.clone();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &[]);
    }));
    assert!(r.is_err(), "expected a constraint violation");
}

#[test]
fn negatives_one_per_family() {
    // Depth 100 → limb q=3, r_off=10. Row 0.
    let os = opens(&[100, 7, 200]);
    let (trace, real, height) = build_trace(&os);
    let air = TableOAir::new(height, real);
    check_constraints(&air, &trace, &[]); // baseline passes
    let w = TABLE_O_WIDTH;

    // Column offsets (match OCols).
    let o_region = 2usize;
    let o_q = o_region + 26; // 28
    let o_roff = o_q + 9; // 37

    // depth relation: corrupt r_off (depth no longer = Σstart·q + r_off).
    expect_violation(&air, &trace, |v| v[o_roff] += BabyBear::ONE);

    // one-hot q: zero the set q bit on row 0 (q=3 for depth 100).
    expect_violation(&air, &trace, |v| v[o_q + 3] = BabyBear::ZERO);

    // zero-suffix: write a nonzero digit into a limb strictly below the
    // boundary (limb 8's first digit; q=3 so limb 8 must reconstruct to 0).
    expect_violation(&air, &trace, |v| v[o_region + 24] = BabyBear::ONE);

    // boundary equation: bump the boundary limb's low digit so region[q] ≠
    // 2·pow_b·H (region digit for limb 3 = digits at o_region + 9).
    expect_violation(&air, &trace, |v| v[o_region + 9] += BabyBear::ONE);

    // padding hygiene (row `real` is padding since height > real).
    if height > real {
        expect_violation(&air, &trace, |v| v[real * w] = BabyBear::ONE);
    }
}

#[test]
fn degree_is_at_most_three() {
    use p3_air::{AirLayout, get_max_constraint_degree};
    let air = TableOAir::new(8, 3);
    let layout = AirLayout {
        main_width: TABLE_O_WIDTH,
        preprocessed_width: TABLE_O_PREP_WIDTH,
        num_public_values: 0,
        ..Default::default()
    };
    let deg = get_max_constraint_degree::<BabyBear, _>(&air, layout);
    assert!(deg <= 3, "O local degree {deg} exceeds 3");
}
