//! Reduced Table A: local constraints over real `build_r3_plan` rows, per-family
//! negatives, and a degree regression. Full bus balance is the M7 round test.

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::plan::OpKind;
use rsmt_witness::r3build::{R3Plan, build_r3_plan};

use super::*;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

fn plan(prefill: usize, batch: usize) -> R3Plan {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(2024);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..prefill)
        .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
        .collect();
    tree.batch_insert(b1);
    let old = tree.root_hash();
    let b2: Vec<KeyValue> = (0..batch)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (applied, proof) = tree.batch_insert(b2);
    let new = tree.root_hash().unwrap();
    build_r3_plan(&proof, &applied, old.as_ref(), &new).unwrap()
}

fn publics(p: &R3Plan) -> Vec<BabyBear> {
    let zero = [BabyBear::ZERO; 8];
    let old = p.old_root.unwrap_or(zero);
    public_values(&old, &p.new_root, p.old_root_is_none)
}

#[test]
fn width_is_33() {
    assert_eq!(TABLE_AR_WIDTH, 33);
    assert_eq!(NUM_PUBLIC, 17);
}

#[test]
fn constraints_pass_on_real_rows() {
    let p = plan(32, 24);
    let (trace, real, height) = build_trace(&p.a_rows);
    let air = TableArAir::new(height, real);
    check_constraints(&air, &trace, &publics(&p));
    // exercised all five opcodes
    for k in [OpKind::S, OpKind::O, OpKind::OL, OpKind::L, OpKind::N] {
        assert!(p.a_rows.iter().any(|r| r.kind == k), "missing {k:?}");
    }
}

fn expect_violation(
    air: &TableArAir,
    trace: &RowMajorMatrix<BabyBear>,
    pubs: &[BabyBear],
    mutate: impl FnOnce(&mut Vec<BabyBear>),
) {
    let mut bad = trace.values.clone();
    mutate(&mut bad);
    let bad_trace = RowMajorMatrix::new(bad, TABLE_AR_WIDTH);
    let air = air.clone();
    let pubs = pubs.to_vec();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &pubs);
    }));
    assert!(r.is_err(), "expected a constraint violation");
}

#[test]
fn negatives_one_per_family() {
    let p = plan(16, 16);
    let (trace, real, height) = build_trace(&p.a_rows);
    let air = TableArAir::new(height, real);
    let pubs = publics(&p);
    check_constraints(&air, &trace, &pubs);
    let w = TABLE_AR_WIDTH;

    let s_row = p.a_rows.iter().position(|r| r.kind == OpKind::S).unwrap();
    let l_row = p.a_rows.iter().position(|r| r.kind == OpKind::L).unwrap();
    let last = real - 1;

    // one-hot: clear the S selector on an S row.
    expect_violation(&air, &trace, &pubs, |v| {
        v[s_row * w + O_IS_S] = BabyBear::ZERO
    });
    // digest shape: break old = new on an S row.
    expect_violation(&air, &trace, &pubs, |v| {
        v[s_row * w + O_NEW] += BabyBear::ONE
    });
    // L old-zero: set a nonzero old limb on an L row.
    expect_violation(&air, &trace, &pubs, |v| {
        v[l_row * w + O_OLD] = BabyBear::ONE
    });
    // subtree_start: corrupt an S row's start (base opcode ⇒ start = row_idx).
    expect_violation(&air, &trace, &pubs, |v| {
        v[s_row * w + O_SST] += BabyBear::ONE
    });
    // boundary: corrupt the last real row's new digest.
    expect_violation(&air, &trace, &pubs, |v| {
        v[last * w + O_NEW] += BabyBear::ONE
    });
    // padding hygiene.
    if height > real {
        expect_violation(&air, &trace, &pubs, |v| {
            v[real * w + O_IS_S] = BabyBear::ONE
        });
    }
}

#[test]
fn degree_is_two() {
    use p3_air::{AirLayout, get_max_constraint_degree};
    let air = TableArAir::new(8, 5);
    let layout = AirLayout {
        main_width: TABLE_AR_WIDTH,
        preprocessed_width: TABLE_AR_PREP_WIDTH,
        num_public_values: NUM_PUBLIC,
        ..Default::default()
    };
    let deg = get_max_constraint_degree::<BabyBear, _>(&air, layout);
    assert_eq!(deg, 2, "reduced A degree must be 2");
}
