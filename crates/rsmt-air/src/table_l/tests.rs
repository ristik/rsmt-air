//! Table L: local `check_constraints` (padding hygiene is the only local rule),
//! a symbolic degree regression, and layout/reconstruction sanity. Full bus
//! balance (range/p2ff/p2term/leaf) is the M7 end-to-end test.

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};

use rsmt_core::{Value32, bytes_to_limbs};
use rsmt_hash::default_perm;
use rsmt_witness::r3arena::PermutationPlan;
use rsmt_witness::r3plan::{R3Leaf, build_leaf, reconstruct_limbs};

use super::*;

fn leaves(n: u32) -> Vec<R3Leaf> {
    let perm = default_perm();
    let mut plan = PermutationPlan::new();
    (0..n)
        .map(|i| {
            let mut kb = [0u8; 32];
            let mut vb = [0u8; 32];
            for b in 0..32 {
                kb[b] = (i as u8).wrapping_add(b as u8).wrapping_mul(31);
                vb[b] = (i as u8)
                    .wrapping_add(b as u8)
                    .wrapping_mul(97)
                    .wrapping_add(3);
            }
            let (leaf, _) =
                build_leaf(&perm, &mut plan, i, &bytes_to_limbs(&kb), &Value32::new(vb));
            leaf
        })
        .collect()
}

#[test]
fn width_is_93() {
    assert_eq!(TABLE_L_WIDTH, 93);
    assert_eq!(TABLE_L_PREP_WIDTH, 1);
}

#[test]
fn constraints_pass_on_real_leaves() {
    let ls = leaves(5);
    let (trace, real, height) = build_trace(&ls);
    let air = TableLAir::new(height, real);
    check_constraints(&air, &trace, &[]);
    assert_eq!(real, 5);
}

#[test]
fn trace_row_reconstructs_leaf() {
    // The built trace's digit columns reconstruct exactly the leaf key/value.
    let ls = leaves(3);
    let (trace, _, _) = build_trace(&ls);
    for (r, leaf) in ls.iter().enumerate() {
        let row = &trace.values[r * TABLE_L_WIDTH..(r + 1) * TABLE_L_WIDTH];
        // a_row_idx column matches.
        assert_eq!(row[0], BabyBear::from_u32(leaf.a_row_idx));
        // reconstruct from the digit columns (as u32) — matches the plan.
        let kd: [u32; 26] = core::array::from_fn(|i| row[1 + i].as_canonical_u32());
        assert_eq!(reconstruct_limbs(&kd), reconstruct_limbs(&leaf.key_digits));
    }
}

#[test]
fn padding_row_must_stay_zero() {
    let ls = leaves(3); // real 3, padded 4 → one padding row
    let (trace, real, height) = build_trace(&ls);
    assert!(height > real);
    let air = TableLAir::new(height, real);
    check_constraints(&air, &trace, &[]); // baseline passes

    // Writing a nonzero into the padding row violates padding hygiene.
    let mut bad = trace.values.clone();
    bad[real * TABLE_L_WIDTH] = BabyBear::ONE; // a_row_idx of padding row
    let bad_trace = p3_matrix::dense::RowMajorMatrix::new(bad, TABLE_L_WIDTH);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &[]);
    }));
    assert!(r.is_err(), "nonzero padding row must fail");
}

#[test]
fn symbolic_degree_is_two() {
    use p3_air::{AirLayout, get_max_constraint_degree};
    let air = TableLAir::new(8, 5);
    let layout = AirLayout {
        main_width: TABLE_L_WIDTH,
        preprocessed_width: TABLE_L_PREP_WIDTH,
        num_public_values: 0,
        ..Default::default()
    };
    let deg = get_max_constraint_degree::<BabyBear, _>(&air, layout);
    // Only the padding-hygiene rule (not_real · cell) is local → degree 2.
    assert_eq!(deg, 2, "L local constraint degree must be 2");
}
