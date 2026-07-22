//! TracePlan tests: invariant checks over honest multi-round histories,
//! self-validation refusal on tampered streams, arena/prefix sharing, and
//! multiplicity totals (DEVPLAN M2 exit criteria).

use p3_field::PrimeCharacteristicRing;
use proptest::prelude::*;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Op, Tree, Value32, bytes_to_limbs};
use rsmt_hash::{Digest, Poseidon2Hasher};

use crate::*;

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

/// Drive `rounds` random batches, building + checking a plan each round.
/// Returns totals for coverage assertions.
fn drive(seed: u64, rounds: usize, sizes: &[usize]) -> (usize, usize, usize, usize) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let mut old_root: Option<Digest> = None;
    let (mut tot_join, mut tot_open, mut tot_ol, mut tot_b11) = (0, 0, 0, 0);

    for r in 0..rounds {
        let n = sizes[r % sizes.len()];
        let batch: Vec<KeyValue> = (0..n)
            .map(|_| {
                (rand_key(&mut rng), {
                    let mut vb = [0u8; 32];
                    rng.fill(vb.as_mut_slice());
                    Value32::new(vb)
                })
            })
            .collect();
        let (applied, proof) = tree.batch_insert(batch);
        let new_root = tree.root_hash();
        if applied.is_empty() {
            continue;
        }
        let nr = new_root.unwrap();
        let plan = build_plan(&proof, &applied, old_root.as_ref(), &nr)
            .unwrap_or_else(|e| panic!("round {r}: build_plan: {e:?}"));
        check_plan_invariants(&plan).unwrap_or_else(|e| panic!("round {r}: invariants: {e}"));

        // publics reflect the boundary
        assert_eq!(plan.publics.new_root, nr);
        assert_eq!(plan.publics.old_root_is_none, old_root.is_none());
        assert_eq!(plan.shape.n_ops, proof.len());
        assert_eq!(plan.a_rows.len(), proof.len());

        tot_join += plan.shape.n_join;
        tot_open += plan.shape.n_open;
        tot_ol += plan.shape.n_ol;
        tot_b11 += plan.shape.n_b11;
        old_root = Some(nr);
    }
    (tot_join, tot_open, tot_ol, tot_b11)
}

#[test]
fn plans_build_and_self_check() {
    let (join, open, ol, b11) = drive(2024, 8, &[1, 3, 17, 200]);
    // A rich history must exercise joins, openings, merges, and b11 junctions.
    assert!(join > 0, "no joins");
    assert!(open > 0, "no openings (O)");
    assert!(ol > 0, "no opened leaves (OL)");
    assert!(b11 > 0, "no pre-existing (b11) junctions");
}

#[test]
fn permutation_budget_and_prefix_sharing() {
    // Single large genesis batch, then a second batch that splits edges.
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(7);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..128)
        .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
        .collect();
    let (a1, _) = tree.batch_insert(b1);
    let r1 = tree.root_hash().unwrap();

    let b2: Vec<KeyValue> = (0..64)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (a2, p2) = tree.batch_insert(b2);
    let r2 = tree.root_hash().unwrap();
    assert!(!a1.is_empty() && !a2.is_empty());

    let plan = build_plan(&p2, &a2, Some(&r1), &r2).unwrap();
    check_plan_invariants(&plan).unwrap();

    // On distinct keys/positions, the arena hits the budget exactly, which is
    // strictly less than the naive count (2 prefix perms per b11 junction).
    let budget = 3 * (plan.shape.n_l + plan.shape.n_ol)
        + 2 * plan.shape.n_join
        + plan.shape.n_b11
        + 2 * plan.shape.n_open;
    assert_eq!(plan.arena.len(), budget, "prefix sharing not realised");

    let naive = 3 * (plan.shape.n_l + plan.shape.n_ol)
        + 3 * plan.shape.n_join // prefix twice + one children for b11, or prefix+children for new
        + plan.shape.n_b11
        + 2 * plan.shape.n_open;
    if plan.shape.n_b11 > 0 {
        assert!(budget < naive, "sharing should save at least one perm");
    }
}

#[test]
fn self_validation_refuses_tampered_stream() {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(11);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let batch: Vec<KeyValue> = (0..32)
        .map(|_| (rand_key(&mut rng), Value32::new([9u8; 32])))
        .collect();
    let (applied, proof) = tree.batch_insert(batch);
    let root = tree.root_hash().unwrap();

    // honest builds
    build_plan(&proof, &applied, None, &root).unwrap();

    // shift an N depth → reference verifier rejects → build_plan refuses.
    let mut bad = proof.clone();
    for op in bad.iter_mut() {
        if let Op::N { depth } = op {
            *depth = (*depth + 1) % 256;
            break;
        }
    }
    match build_plan(&bad, &applied, None, &root) {
        Err(PlanError::Rejected(_)) => {}
        other => panic!("expected Rejected, got {other:?}"),
    }

    // wrong new root → refused.
    let mut wrong = root;
    wrong[0] += p3_baby_bear::BabyBear::ONE;
    match build_plan(&proof, &applied, None, &wrong) {
        Err(PlanError::Rejected(_)) => {}
        other => panic!("expected Rejected on wrong root, got {other:?}"),
    }
}

#[test]
fn determinism() {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(3);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let batch: Vec<KeyValue> = (0..48)
        .map(|_| (rand_key(&mut rng), Value32::new([5u8; 32])))
        .collect();
    let (applied, proof) = tree.batch_insert(batch);
    let root = tree.root_hash().unwrap();
    let p1 = build_plan(&proof, &applied, None, &root).unwrap();
    let p2 = build_plan(&proof, &applied, None, &root).unwrap();
    assert_eq!(p1.shape, p2.shape);
    assert_eq!(p1.arena.len(), p2.arena.len());
    assert_eq!(p1.r_mults, p2.r_mults);
    assert_eq!(p1.p_mults, p2.p_mults);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn prop_plan_invariants_hold(seed in any::<u64>()) {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
        let mut tree: Tree<Poseidon2Hasher> = Tree::new();
        let mut old: Option<Digest> = None;
        for _ in 0..3 {
            let n = 1 + (rng.random::<u32>() % 40) as usize;
            let batch: Vec<KeyValue> =
                (0..n).map(|_| (rand_key(&mut rng), { let mut vb = [0u8; 32]; rng.fill(vb.as_mut_slice()); Value32::new(vb) })).collect();
            let (applied, proof) = tree.batch_insert(batch);
            let nr = tree.root_hash();
            if applied.is_empty() { continue; }
            let nr = nr.unwrap();
            let plan = build_plan(&proof, &applied, old.as_ref(), &nr).unwrap();
            prop_assert!(check_plan_invariants(&plan).is_ok());
            old = Some(nr);
        }
    }
}
