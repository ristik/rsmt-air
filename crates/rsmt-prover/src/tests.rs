//! End-to-end round proving tests (DEVPLAN M4). These exercise the real FRI
//! stack (not `check_constraints`): preprocessed commitments, public values,
//! degree budgets, and verification.

use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, bytes_to_limbs};
use rsmt_hash::{Digest, Poseidon2Hasher};
use rsmt_witness::{TracePlan, build_plan};

use crate::config::ProverConfig;
use crate::proof_hash::Poseidon2ProofHash;
use crate::round::prove_and_verify_round;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

/// A two-round plan rich in opcodes (S, O, OL, L, N) over a prefilled tree.
fn rich_plan(seed: u64, prefill: usize, batch: usize) -> (TracePlan, Option<Digest>, Digest) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..prefill)
        .map(|_| (rand_key(&mut rng), vec![1u8; 8]))
        .collect();
    tree.batch_insert(b1);
    let old = tree.root_hash();
    let b2: Vec<KeyValue> = (0..batch)
        .map(|_| (rand_key(&mut rng), vec![2u8; 8]))
        .collect();
    let (applied, proof) = tree.batch_insert(b2);
    let new = tree.root_hash().unwrap();
    let plan = build_plan(&proof, &applied, old.as_ref(), &new).unwrap();
    (plan, old, new)
}

#[test]
fn genesis_round_proves_and_verifies() {
    let (plan, _old, _new) = rich_plan(1, 0, 16);
    let cfg = ProverConfig::default();
    prove_and_verify_round::<Poseidon2ProofHash>(&plan, 1, &cfg).expect("prove+verify");
}

#[test]
fn prefilled_round_proves_and_verifies() {
    let (plan, _old, _new) = rich_plan(2, 64, 24);
    // sanity: the round exercised all opcode kinds
    assert!(plan.shape.n_join > 0 && plan.shape.n_open > 0 && plan.shape.n_ol > 0);
    let cfg = ProverConfig::default();
    prove_and_verify_round::<Poseidon2ProofHash>(&plan, 2, &cfg).expect("prove+verify");
}
