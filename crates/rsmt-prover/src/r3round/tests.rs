//! End-to-end R3 round proof: build a real plan and prove+verify with full
//! seven-bus balance (A/B/L/J/O/R/P). If any bus tuple were wrong, LogUp balance
//! would fail here.

use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::r3build::build_r3_plan;

use super::*;
use crate::config::ProverConfig;
use crate::proof_hash::Poseidon2ProofHash;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

fn prove_round(seed: u64, prefill: usize, batch: usize) -> Result<(), String> {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
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
    let plan = build_r3_plan(&proof, &applied, old.as_ref(), &new).expect("plan");
    prove_and_verify_r3_round::<Poseidon2ProofHash>(&plan, 42, &ProverConfig::default())
}

#[test]
fn genesis_round_proves_and_verifies() {
    prove_round(1, 0, 8).expect("genesis round");
}

#[test]
fn prefilled_round_proves_and_verifies() {
    // Rich in S/O/OL/L/N.
    prove_round(2, 64, 16).expect("prefilled round");
}
