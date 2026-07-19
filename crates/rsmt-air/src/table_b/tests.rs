//! Table B: the inner Poseidon2 AIR accepts the arena trace, the output
//! columns match the arena outputs (so Bus 2 will bind in M4), and a tampered
//! output lane is rejected.

use p3_air::check_constraints;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs};
use rsmt_hash::{Poseidon2Hasher, STATE_WIDTH};
use rsmt_witness::{TracePlan, build_plan};

use super::*;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

fn rich_plan() -> TracePlan {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(303);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..64)
        .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
        .collect();
    tree.batch_insert(b1);
    let r1 = tree.root_hash().unwrap();
    let b2: Vec<KeyValue> = (0..32)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (a2, p2) = tree.batch_insert(b2);
    let r2 = tree.root_hash().unwrap();
    build_plan(&p2, &a2, Some(&r1), &r2).unwrap()
}

#[test]
fn poseidon2_air_accepts_arena_and_outputs_match() {
    let plan = rich_plan();
    let inputs = collect_inputs(&plan);
    assert!(!inputs.is_empty());
    let (trace, real, height) = build_trace(&inputs);
    let air = TableBAir::new(height, real, collect_modes(&plan));
    check_constraints(&air, &trace, &[]);

    // Every real perm's output columns equal the arena output (Bus 2 tuple).
    let arena = plan.arena.entries();
    for (p, io) in arena.iter().enumerate() {
        let row = p / P2_VECTOR_LEN;
        let lane = p % P2_VECTOR_LEN;
        let base = lane * P2_PERM_WIDTH + P2_OUTPUT_OFFSET;
        for j in 0..STATE_WIDTH {
            let cell = trace.values[row * trace.width + base + j];
            assert_eq!(cell, io.output[j], "perm {p} output limb {j}");
        }
    }
}

#[test]
fn tampered_output_is_rejected() {
    let plan = rich_plan();
    let inputs = collect_inputs(&plan);
    let (trace, real, height) = build_trace(&inputs);
    let air = TableBAir::new(height, real, collect_modes(&plan));

    let mut bad = trace.values.clone();
    // Corrupt lane 0's output state on row 0.
    bad[P2_OUTPUT_OFFSET] += BabyBear::ONE;
    let bad_trace = p3_matrix::dense::RowMajorMatrix::new(bad, trace.width);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_constraints(&air, &bad_trace, &[]);
    }));
    assert!(
        r.is_err(),
        "a corrupted Poseidon2 output must violate the AIR"
    );
}
