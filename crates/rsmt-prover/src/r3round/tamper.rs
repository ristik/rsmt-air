//! R3 adversarial sweep (M8): apply one mutation to a freshly-built trace and
//! require the proof to be **rejected** — by a local constraint (which makes the
//! internal `check_constraints` panic during `prove_batch`) or by a LogUp bus
//! imbalance (which makes `verify_batch` return `Err`). The honest identity hook
//! must still verify.
//!
//! Each class targets a different soundness surface: the public boundary, the
//! post-order chain (S2), the leaf binding (S4/bus), the opened region (S5), the
//! join coherence (S6), and the range/pow2 fixed-table balances (S9).

use std::panic::{AssertUnwindSafe, catch_unwind};

use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::plan::OpKind;
use rsmt_witness::r3build::{R3Plan, build_r3_plan};

use super::{R3RoundTraces, prove_and_verify_r3_round, prove_and_verify_r3_round_with};
use crate::config::ProverConfig;
use crate::proof_hash::Poseidon2ProofHash;

// Main-trace widths (must track each table's `*_WIDTH`).
const AW: usize = 33;
const LW: usize = 93;
const JW: usize = 142;
const OW: usize = 89;
// A column offsets.
const A_NEW: usize = 13;
const A_SST: usize = 32;
// L / J / O column offsets.
const L_DIGEST: usize = 85;
const J_H: usize = 24;
const O_REGION: usize = 2;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

/// A round rich in S/O/OL/L/N.
fn rich_plan() -> R3Plan {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(2024);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..64)
        .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
        .collect();
    tree.batch_insert(b1);
    let old = tree.root_hash();
    let b2: Vec<KeyValue> = (0..24)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (applied, proof) = tree.batch_insert(b2);
    let new = tree.root_hash().unwrap();
    build_r3_plan(&proof, &applied, old.as_ref(), &new).unwrap()
}

/// True iff the tampered round is rejected (panic during prove, or verify Err).
fn rejected(plan: &R3Plan, tamper: impl FnOnce(&mut R3RoundTraces<'_>)) -> bool {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = catch_unwind(AssertUnwindSafe(|| {
        prove_and_verify_r3_round_with::<Poseidon2ProofHash>(
            plan,
            42,
            &ProverConfig::default(),
            tamper,
        )
    }));
    std::panic::set_hook(prev);
    !matches!(r, Ok(Ok(())))
}

#[test]
fn honest_round_verifies() {
    let plan = rich_plan();
    prove_and_verify_r3_round::<Poseidon2ProofHash>(&plan, 42, &ProverConfig::default())
        .expect("honest round");
    // Sanity: the round really is rich.
    assert!(plan.shape.n_open > 0, "no openings");
    assert!(plan.shape.n_join > 0, "no joins");
}

#[test]
fn tamper_a_new_root() {
    // Corrupt the last real A row's new digest → public boundary fails.
    let plan = rich_plan();
    let last = plan.a_rows.len() - 1;
    assert!(rejected(&plan, |t| {
        t.a.values[last * AW + A_NEW] += BabyBear::ONE;
    }));
}

#[test]
fn tamper_a_subtree_start() {
    // Corrupt row 0's subtree_start (a base opcode ⇒ start = row_idx) → S2 chain.
    let plan = rich_plan();
    assert!(rejected(&plan, |t| {
        t.a.values[A_SST] += BabyBear::ONE;
    }));
}

#[test]
fn tamper_l_digest() {
    // Corrupt a leaf digest → leaf bus (A) and p2term (B) both mismatch.
    let plan = rich_plan();
    assert!(rejected(&plan, |t| {
        t.l.values[L_DIGEST] += BabyBear::ONE;
    }));
}

#[test]
fn tamper_o_region() {
    // Corrupt an opening's region digit → O boundary / p2ff / parent bus.
    let plan = rich_plan();
    assert!(plan.shape.n_open > 0);
    assert!(rejected(&plan, |t| {
        t.o.values[O_REGION] += BabyBear::ONE;
    }));
}

#[test]
fn tamper_j_coherence() {
    // Corrupt a join's shared prefix H → region[q] = 2·pow_b·H fails (S6).
    let plan = rich_plan();
    assert!(plan.shape.n_join > 0);
    assert!(rejected(&plan, |t| {
        t.j.values[J_H] += BabyBear::ONE;
    }));
}

#[test]
fn tamper_range_multiplicity() {
    // Inflate a Table-R send multiplicity → range bus imbalance (S9).
    let plan = rich_plan();
    assert!(rejected(&plan, |t| {
        t.r.values[0] += BabyBear::ONE;
    }));
}

#[test]
fn tamper_pow2_multiplicity() {
    // Inflate a Table-P send multiplicity → pow2 bus imbalance (S9).
    let plan = rich_plan();
    assert!(rejected(&plan, |t| {
        t.p.values[0] += BabyBear::ONE;
    }));
}

const A_DELTA: usize = 22;

#[test]
fn tamper_a_parent_delta() {
    // Corrupt an N row's delta (free locally) → the parent bus no longer matches
    // Table J's depth send (S3 advice/digest co-binding).
    let plan = rich_plan();
    let n_row = plan
        .a_rows
        .iter()
        .position(|r| r.kind == OpKind::N)
        .unwrap();
    assert!(rejected(&plan, |t| {
        t.a.values[n_row * AW + A_DELTA] += BabyBear::ONE;
    }));
}

#[test]
fn tamper_b_input() {
    // Corrupt a Poseidon2 input in Table B → B's own permutation constraint and
    // the p2 bus (L/J/O expected the original output) both break (S8).
    let plan = rich_plan();
    assert!(rejected(&plan, |t| {
        t.b.values[0] += BabyBear::ONE;
    }));
}

/// Differential fuzzing (M8): a single `+1` to *any* real cell of A/L/J/O must be
/// rejected — there is no class-6 free cell, so every mutation breaks either a
/// local constraint or a bus. Full prove+verify per mutation, so kept modest.
#[test]
fn differential_fuzz_random_cell_mutations_rejected() {
    let plan = rich_plan();
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0xF0F0);
    // (width, real_rows) per table, indexed 0..4 = A/L/J/O.
    let dims: [(usize, usize); 4] = [
        (AW, plan.a_rows.len()),
        (LW, plan.leaves.len()),
        (JW, plan.joins.len()),
        (OW, plan.opens.len()),
    ];
    for _ in 0..8 {
        let which = (rng.random::<u32>() % 4) as usize;
        let (w, real) = dims[which];
        let idx = (rng.random::<u32>() as usize % real) * w + (rng.random::<u32>() as usize % w);
        let ok = rejected(&plan, |t| {
            let tr = match which {
                0 => &mut *t.a,
                1 => &mut *t.l,
                2 => &mut *t.j,
                _ => &mut *t.o,
            };
            tr.values[idx] += BabyBear::ONE;
        });
        assert!(ok, "table {which} cell {idx} mutation was not rejected");
    }
}

/// Honest rounds over several shapes all verify (the completeness side of the
/// differential test).
#[test]
fn honest_rounds_over_shapes_verify() {
    for (seed, prefill, batch) in [(1u64, 0, 4), (2, 0, 32), (3, 16, 8), (4, 256, 12)] {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
        let mut tree: Tree<Poseidon2Hasher> = Tree::new();
        let b1: Vec<KeyValue> = (0..prefill)
            .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
            .collect();
        tree.batch_insert(b1);
        let old = tree.root_hash();
        let b2: Vec<KeyValue> = (0..batch)
            .map(|_| (rand_key(&mut rng), Value32::new([9u8; 32])))
            .collect();
        let (applied, proof) = tree.batch_insert(b2);
        let new = tree.root_hash().unwrap();
        let plan = build_r3_plan(&proof, &applied, old.as_ref(), &new).unwrap();
        prove_and_verify_r3_round::<Poseidon2ProofHash>(&plan, 7, &ProverConfig::default())
            .unwrap_or_else(|e| panic!("shape (seed {seed}) failed: {e}"));
    }
}

// Keep the width constants honest against the real layouts.
const _: () = {
    assert!(AW == rsmt_air::table_ar::TABLE_AR_WIDTH);
    assert!(LW == rsmt_air::table_l::TABLE_L_WIDTH);
    assert!(JW == rsmt_air::table_j::TABLE_J_WIDTH);
    assert!(OW == rsmt_air::table_o::TABLE_O_WIDTH);
};
