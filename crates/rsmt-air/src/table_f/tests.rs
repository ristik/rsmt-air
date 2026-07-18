//! Table F (R10 coherence): positive `check_constraints` over a real plan plus
//! per-family negatives.

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::{TracePlan, build_plan};

use super::*;

// Column offsets (must match FCols field order).
const O_LS: usize = 1;
const O_DEPTH: usize = 3;
const O_R_OFF: usize = 22;
const O_H: usize = 24;
const O_B11: usize = 102;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

fn rich_plan() -> TracePlan {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(404);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..96)
        .map(|_| (rand_key(&mut rng), vec![1u8; 8]))
        .collect();
    tree.batch_insert(b1);
    let r1 = tree.root_hash().unwrap();
    let b2: Vec<KeyValue> = (0..48)
        .map(|_| (rand_key(&mut rng), vec![2u8; 8]))
        .collect();
    let (a2, p2) = tree.batch_insert(b2);
    let r2 = tree.root_hash().unwrap();
    build_plan(&p2, &a2, Some(&r1), &r2).unwrap()
}

fn expect_violation(
    air: &TableFAir,
    trace: &RowMajorMatrix<BabyBear>,
    mutate: impl FnOnce(&mut Vec<BabyBear>),
) {
    let mut bad = trace.values.clone();
    mutate(&mut bad);
    let bad_trace = RowMajorMatrix::new(bad, TABLE_F_WIDTH);
    let air = air.clone();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &[]);
    }));
    assert!(r.is_err(), "expected a constraint violation");
}

#[test]
fn constraints_pass_on_real_plan() {
    let plan = rich_plan();
    assert!(!plan.f_joins.is_empty() && !plan.f_opens.is_empty());
    let (trace, n_join, n_open, height) = build_trace(&plan);
    let air = TableFAir::new(height, n_join, n_open);
    check_constraints(&air, &trace, &[]);
}

#[test]
fn negatives_one_per_family() {
    let plan = rich_plan();
    let (trace, n_join, n_open, height) = build_trace(&plan);
    let air = TableFAir::new(height, n_join, n_open);
    check_constraints(&air, &trace, &[]);

    let w = TABLE_F_WIDTH;
    let real = n_join + n_open;

    // depth-from-q: corrupt r_off on a join row.
    expect_violation(&air, &trace, |v| v[O_R_OFF] += BabyBear::ONE);
    // depth column.
    expect_violation(&air, &trace, |v| v[O_DEPTH] += BabyBear::ONE);
    // D19: opening leaf's own subtree_start (ls = parent_row_idx).
    if n_open > 0 {
        expect_violation(&air, &trace, |v| v[n_join * w + O_LS] += BabyBear::ONE);
    }
    // case algebra: b11.
    expect_violation(&air, &trace, |v| v[O_B11] += BabyBear::ONE);
    // R10 coherence: corrupt the shared prefix H → boundary equations break.
    expect_violation(&air, &trace, |v| v[O_H] += BabyBear::ONE);
    // cross-kind zeroing: nonzero b11 on an opening row.
    if n_open > 0 {
        expect_violation(&air, &trace, |v| v[n_join * w + O_B11] = BabyBear::ONE);
    }
    // padding hygiene.
    if height > real {
        expect_violation(&air, &trace, |v| v[real * w + O_DEPTH] = BabyBear::ONE);
    }
}
