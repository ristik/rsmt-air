//! Table A: positive `check_constraints` over a real plan, and one hand-picked
//! negative per constraint family (DEVPLAN M3 exit criteria).

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::{OpKind, TracePlan, build_plan};

use super::*;

// Column offsets (must match the ACols field order).
const O_IS_S: usize = 0;
const O_OLD: usize = 5;
const O_NEW: usize = 13;
const O_OLD_IS_NONE: usize = 21;
const O_BATCH_IDX: usize = 33;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

/// Build a two-round plan rich in opcodes (S, O, OL, L, N).
fn rich_plan() -> TracePlan {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(2024);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..96)
        .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
        .collect();
    tree.batch_insert(b1);
    let r1 = tree.root_hash().unwrap();
    let b2: Vec<KeyValue> = (0..48)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (a2, p2) = tree.batch_insert(b2);
    let r2 = tree.root_hash().unwrap();
    build_plan(&p2, &a2, Some(&r1), &r2).unwrap()
}

fn find_kind(plan: &TracePlan, kind: OpKind) -> usize {
    plan.a_rows
        .iter()
        .position(|r| r.kind == kind)
        .expect("kind present")
}

fn expect_violation(
    air: &TableAAir,
    trace: &p3_matrix::dense::RowMajorMatrix<BabyBear>,
    pubs: &[BabyBear],
    mutate: impl FnOnce(&mut Vec<BabyBear>),
) {
    let mut bad = trace.values.clone();
    mutate(&mut bad);
    let bad_trace = p3_matrix::dense::RowMajorMatrix::new(bad, TABLE_A_WIDTH);
    let air = air.clone();
    let pubs = pubs.to_vec();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &pubs);
    }));
    assert!(r.is_err(), "expected a constraint violation");
}

#[test]
fn constraints_pass_on_real_plan() {
    let plan = rich_plan();
    let (trace, real, height) = build_trace(&plan.a_rows);
    let air = TableAAir::new(height, real);
    let pubs = public_values(&plan.publics);
    check_constraints(&air, &trace, &pubs);

    // sanity: the plan actually exercised all five opcodes
    for k in [OpKind::S, OpKind::O, OpKind::OL, OpKind::L, OpKind::N] {
        assert!(plan.a_rows.iter().any(|r| r.kind == k), "missing {k:?}");
    }
}

#[test]
fn negatives_one_per_family() {
    let plan = rich_plan();
    let (trace, real, height) = build_trace(&plan.a_rows);
    let air = TableAAir::new(height, real);
    let pubs = public_values(&plan.publics);
    check_constraints(&air, &trace, &pubs); // baseline passes

    let w = TABLE_A_WIDTH;
    let s_row = find_kind(&plan, OpKind::S);
    let l_row = find_kind(&plan, OpKind::L);
    let n_row = find_kind(&plan, OpKind::N);
    let last = real - 1;

    // one-hot: clear the S selector on an S row.
    expect_violation(&air, &trace, &pubs, |v| {
        v[s_row * w + O_IS_S] = BabyBear::ZERO
    });

    // digest shape: break old = new on an S row.
    expect_violation(&air, &trace, &pubs, |v| {
        v[s_row * w + O_NEW] += BabyBear::ONE;
    });

    // L old_is_none shape: clear it on an L row (also breaks old==0? no, old already 0).
    expect_violation(&air, &trace, &pubs, |v| {
        v[l_row * w + O_OLD_IS_NONE] = BabyBear::ZERO
    });

    // L old-zero: set a nonzero old limb on an L row (old_is_none ⇒ old = 0).
    expect_violation(&air, &trace, &pubs, |v| {
        v[l_row * w + O_OLD] = BabyBear::ONE
    });

    // link zeroing: nonzero batch_idx on an N row.
    expect_violation(&air, &trace, &pubs, |v| {
        v[n_row * w + O_BATCH_IDX] = BabyBear::ONE
    });

    // boundary: corrupt the last real row's new digest.
    expect_violation(&air, &trace, &pubs, |v| {
        v[last * w + O_NEW] += BabyBear::ONE
    });

    // padding hygiene: write into a padding row (if any).
    if height > real {
        expect_violation(&air, &trace, &pubs, |v| {
            v[real * w + O_IS_S] = BabyBear::ONE
        });
    }
}
