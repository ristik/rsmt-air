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

/// Cross-process verification (M7 exit criterion): prove in "process 1",
/// serialize the proof to bytes, then verify in "process 2" that receives ONLY
/// the bytes, the public inputs, and the scalar shape — no plan, no `ProverData`.
#[test]
fn cross_process_verify_from_bytes() {
    use p3_batch_stark::BatchProof;
    use p3_field::PrimeCharacteristicRing;
    use rsmt_air::table_ar;

    use crate::proof_hash::{F, Poseidon2Config};

    // -- process 1 (prover) --
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(5);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    tree.batch_insert(
        (0..48)
            .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
            .collect(),
    );
    let old = tree.root_hash();
    let batch: Vec<KeyValue> = (0..16)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (applied, proof_ops) = tree.batch_insert(batch);
    let new = tree.root_hash().unwrap();
    let plan = build_r3_plan(&proof_ops, &applied, old.as_ref(), &new).unwrap();

    let proof = prove_r3_round::<Poseidon2ProofHash>(&plan, 42, &ProverConfig::default());
    let shape = plan.shape;
    let old_root = plan.old_root.unwrap_or([F::ZERO; 8]);
    let publics = table_ar::public_values(&old_root, &plan.new_root, plan.old_root_is_none);
    let bytes = bincode::serde::encode_to_vec(&proof, bincode::config::standard()).unwrap();

    // -- process 2 (verifier): only bytes + shape + publics + fixed protocol seed --
    let (proof2, _): (BatchProof<Poseidon2Config>, usize) =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard()).unwrap();
    verify_r3_round::<Poseidon2ProofHash>(42, &ProverConfig::default(), &shape, &publics, &proof2)
        .expect("cross-process verify");

    // Negative: a tampered public root must fail.
    let mut bad_publics = publics.clone();
    bad_publics[8] += F::ONE; // first limb of new_root
    assert!(
        verify_r3_round::<Poseidon2ProofHash>(
            42,
            &ProverConfig::default(),
            &shape,
            &bad_publics,
            &proof2
        )
        .is_err(),
        "wrong public root must be rejected"
    );
}

/// M10 FRI parameter grid: prove/verify/proof-size for the R3 round under
/// several FRI configurations that all meet the ~116-bit conjectured target,
/// including the §6.4-preferred **no-grinding** candidates. Run with
/// `--nocapture` (release) to read the numbers.
#[test]
fn m10_fri_grid() {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(7);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    tree.batch_insert(
        (0..1024)
            .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
            .collect(),
    );
    let old = tree.root_hash();
    let batch: Vec<KeyValue> = (0..64)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (applied, proof_ops) = tree.batch_insert(batch);
    let new = tree.root_hash().unwrap();
    let plan = build_r3_plan(&proof_ops, &applied, old.as_ref(), &new).unwrap();

    // (log_blowup, num_queries, query_pow_bits) — conjectured bits = lb·q + pow.
    let grid = [
        (1usize, 100usize, 16usize), // old baseline (has grinding)
        (1, 116, 0),                 // no-grind, blowup 1
        (2, 58, 0),                  // blowup 2, no-grind, 116 bits
        (2, 64, 0),                  // blowup 2, no-grind, 128 bits (clean)
    ];
    eprintln!("M10 FRI grid (prefill=1024 batch=64):");
    eprintln!("  lb  q  pow  bits  prove_ms verify_ms proof_KB");
    for (lb, q, pow) in grid {
        let cfg = ProverConfig {
            log_blowup: lb,
            num_queries: q,
            query_proof_of_work_bits: pow,
            ..ProverConfig::default()
        };
        let bits = lb * q + pow;
        let t0 = std::time::Instant::now();
        let proof = prove_r3_round::<Poseidon2ProofHash>(&plan, 42, &cfg);
        let prove_ms = t0.elapsed().as_secs_f64() * 1e3;
        let bytes = bincode::serde::encode_to_vec(&proof, bincode::config::standard()).unwrap();
        let old_root = plan.old_root.unwrap_or([F::ZERO; 8]);
        let publics =
            rsmt_air::table_ar::public_values(&old_root, &plan.new_root, plan.old_root_is_none);
        let t1 = std::time::Instant::now();
        verify_r3_round::<Poseidon2ProofHash>(42, &cfg, &plan.shape, &publics, &proof)
            .expect("verify");
        let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
        eprintln!(
            "  {lb:>2} {q:>3} {pow:>3} {bits:>5} {prove_ms:>9.1} {verify_ms:>9.1} {:>8.1}",
            bytes.len() as f64 / 1024.0
        );
    }
}

use crate::proof_hash::F;
use p3_field::PrimeCharacteristicRing as _;

/// Print the per-table cost breakdown + prove/verify timing for the M0 baseline
/// scenario (prefill 1024, batch 64). Run with `--nocapture` to read the numbers.
#[test]
fn r3_cost_report() {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(7);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..1024)
        .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
        .collect();
    tree.batch_insert(b1);
    let old = tree.root_hash();
    let b2: Vec<KeyValue> = (0..64)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (applied, proof) = tree.batch_insert(b2);
    let new = tree.root_hash().unwrap();
    let plan = build_r3_plan(&proof, &applied, old.as_ref(), &new).unwrap();

    let cells = super::r3_round_cells(&plan);
    let total: usize = cells.iter().map(|t| t.cells()).sum();
    eprintln!("R3 cost (prefill=1024 batch=64): shape={:?}", plan.shape);
    eprintln!("  T  real padded main prep    cells");
    for t in &cells {
        eprintln!(
            "  {:>2} {:>5} {:>6} {:>4} {:>4} {:>8}",
            t.name,
            t.real,
            t.padded,
            t.main,
            t.prep,
            t.cells()
        );
    }
    let t0 = std::time::Instant::now();
    prove_and_verify_r3_round::<Poseidon2ProofHash>(&plan, 42, &ProverConfig::default())
        .expect("round");
    eprintln!("  total cells={total}  prove+verify={:?}", t0.elapsed());
}
