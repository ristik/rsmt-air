//! `build_r3_plan` tests: real rounds build a consistent plan, the occurrence
//! budget and shape identities hold, and a tampered stream is rejected.

use p3_field::PrimeCharacteristicRing;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;

use super::*;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

/// A prefilled tree + a fresh batch, returning the round's proof/roots/batch.
fn round(
    seed: u64,
    prefill: usize,
    batch: usize,
) -> (
    Vec<rsmt_core::Op<rsmt_hash::Digest>>,
    Vec<KeyValue>,
    Option<rsmt_hash::Digest>,
    rsmt_hash::Digest,
) {
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
    (proof, applied, old, new)
}

#[test]
fn plan_builds_for_real_rounds_and_invariants_hold() {
    // Genesis, small, and a prefilled round rich in S/O/OL/L/N.
    for (prefill, batch) in [(0, 8), (0, 64), (32, 16), (1024, 48)] {
        let (proof, applied, old, new) = round(7, prefill, batch);
        let plan = build_r3_plan(&proof, &applied, old.as_ref(), &new).expect("plan builds");
        check_r3_invariants(&plan).expect("invariants hold");

        // Shape identities.
        let s = &plan.shape;
        assert_eq!(s.n_ops, proof.len());
        assert_eq!(s.n_leaf, plan.leaves.len());
        assert_eq!(s.n_p2ff, 2 * s.n_leaf + s.n_join + s.n_open);
        assert_eq!(s.n_p2term, s.n_leaf + s.n_join + s.n_b11 + s.n_open);
        assert!(s.n_b11 <= s.n_join);
        // Exact permutation budget.
        assert_eq!(
            plan.arena.n_perm(),
            3 * s.n_leaf + 2 * s.n_join + s.n_b11 + 2 * s.n_open
        );
        // The A-row count decomposes into the opcode kinds.
        let n_s = plan.a_rows.iter().filter(|r| r.kind == OpKind::S).count();
        assert_eq!(s.n_ops, n_s + s.n_open + s.n_leaf + s.n_join);

        // Range/pow tallies are nonzero for a real round and don't wrap.
        assert!(plan.r_mults.iter().any(|&m| m > 0));
        assert_eq!(
            plan.p_mults.iter().map(|&m| m as usize).sum::<usize>(),
            s.n_join + s.n_open
        );
    }
}

#[test]
fn leaf_keys_are_strictly_increasing_in_a_order() {
    // Lemma B (new-leaf ordering): the L-row keys, in A-order, strictly increase.
    let (proof, applied, old, new) = round(3, 0, 200);
    let plan = build_r3_plan(&proof, &applied, old.as_ref(), &new).unwrap();
    let l_keys: Vec<Key> = plan
        .a_rows
        .iter()
        .filter(|r| r.kind == OpKind::L)
        .map(|r| r.rho)
        .collect();
    for w in l_keys.windows(2) {
        assert!(w[0] < w[1], "L keys not strictly increasing in A-order");
    }
    assert_eq!(l_keys.len(), applied.len());
}

#[test]
fn tampered_stream_is_rejected() {
    let (mut proof, applied, old, new) = round(9, 16, 24);
    // Corrupt an N depth → the reference verifier rejects, so no plan is built.
    if let Some(rsmt_core::Op::N { depth }) = proof
        .iter_mut()
        .find(|o| matches!(o, rsmt_core::Op::N { .. }))
    {
        *depth = (*depth + 1) % 256;
    }
    let r = build_r3_plan(&proof, &applied, old.as_ref(), &new);
    assert!(matches!(r, Err(R3PlanError::Rejected(_))));
}

#[test]
fn wrong_root_is_rejected() {
    let (proof, applied, old, mut new) = round(11, 8, 8);
    new[0] += p3_baby_bear::BabyBear::from_u32(1);
    let r = build_r3_plan(&proof, &applied, old.as_ref(), &new);
    assert!(matches!(r, Err(R3PlanError::Rejected(_))));
}
