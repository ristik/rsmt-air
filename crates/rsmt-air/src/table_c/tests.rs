//! Table C: positive `check_constraints` over a real plan (batch + opened
//! leaves) plus per-family negatives.

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::{TracePlan, build_plan};

use super::*;

const O_KEY: usize = 0;
const O_STATE_IN: usize = 18;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

fn rich_plan() -> TracePlan {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(101);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..80)
        .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
        .collect();
    tree.batch_insert(b1);
    let r1 = tree.root_hash().unwrap();
    let b2: Vec<KeyValue> = (0..40)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (a2, p2) = tree.batch_insert(b2);
    let r2 = tree.root_hash().unwrap();
    build_plan(&p2, &a2, Some(&r1), &r2).unwrap()
}

fn expect_violation(
    air: &TableCAir,
    trace: &RowMajorMatrix<BabyBear>,
    mutate: impl FnOnce(&mut Vec<BabyBear>),
) {
    let mut bad = trace.values.clone();
    mutate(&mut bad);
    let bad_trace = RowMajorMatrix::new(bad, TABLE_C_WIDTH);
    let air = air.clone();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &[]);
    }));
    assert!(r.is_err(), "expected a constraint violation");
}

#[test]
fn constraints_pass_on_real_plan() {
    let plan = rich_plan();
    assert!(!plan.c_batch.is_empty() && !plan.c_opened.is_empty());
    let (trace, real, height, batch_rows) = build_trace(&plan);
    let air = TableCAir::new(height, real, batch_rows);
    check_constraints(&air, &trace, &[]);
}

#[test]
fn negatives_one_per_family() {
    let plan = rich_plan();
    let (trace, real, height, batch_rows) = build_trace(&plan);
    let air = TableCAir::new(height, real, batch_rows);
    check_constraints(&air, &trace, &[]);

    let w = TABLE_C_WIDTH;

    // step-0 init: corrupt state_in[0] on the first step-0 row.
    expect_violation(&air, &trace, |v| v[O_STATE_IN] += BabyBear::ONE);

    // step transition: corrupt state_in[0] on a step-1 row (row 1).
    expect_violation(&air, &trace, |v| v[w + O_STATE_IN] += BabyBear::ONE);

    // continuity: change the key on a step-1 row (row 1) only.
    expect_violation(&air, &trace, |v| v[w + O_KEY] += BabyBear::ONE);

    // padding hygiene.
    if height > real {
        expect_violation(&air, &trace, |v| v[real * w + O_STATE_IN] = BabyBear::ONE);
    }
}
