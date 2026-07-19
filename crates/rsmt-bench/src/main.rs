//! `rsmt-bench` — CLI benchmarks for the RSMT v6a arithmetization (DEVPLAN M6).
//!
//! Subcommands:
//! - `smt`: CPU-only — prefill a tree, apply a batch, verify the consistency proof (no ZK).
//! - `round`: one end-to-end batch-STARK round (all 8 tables, 7 buses) with a per-table
//!   real/padded/width/cells breakdown, timings, and proof size.
//! - `perf`: sweep batch sizes (and/or proof hashes) through `round`.

use std::time::{Duration, Instant};

use clap::{Parser, Subcommand, ValueEnum};
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;
use tracing_forest::ForestLayer;
use tracing_forest::util::LevelFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

use rsmt_core::{Key, KeyValue, Tree, Value32, bytes_to_limbs, verify_consistency};
use rsmt_hash::Poseidon2Hasher;
use rsmt_prover::config::ProverConfig;
use rsmt_prover::proof_hash::{Blake3ProofHash, Poseidon2ProofHash, ProvingHash, Sha256ProofHash};
use rsmt_prover::{prove_r3_round, r3_round_cells, verify_r3_round};
use rsmt_witness::r3build::{R3Plan, build_r3_plan};

#[derive(Parser, Debug)]
#[command(version, about = "RSMT v6a arithmetization benchmarks")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// CPU-only: prefill SMT, insert batch, verify consistency proof.
    Smt {
        #[arg(long, default_value_t = 10_000)]
        prefill: usize,
        #[arg(long, default_value_t = 1_000)]
        batch: usize,
        #[arg(long, default_value_t = 0)]
        seed: u64,
    },
    /// One end-to-end batch-STARK round with a per-table metrics breakdown.
    Round {
        #[arg(long, default_value_t = 64)]
        batch: usize,
        #[arg(long, default_value_t = 0)]
        prefill: usize,
        #[arg(long, default_value_t = 0)]
        seed: u64,
        #[command(flatten)]
        fri: FriArgs,
        #[arg(long, value_enum, default_value_t = HashArg::Poseidon2)]
        hash: HashArg,
    },
    /// Sweep batch sizes (and/or proof hashes) through `round`.
    Perf {
        /// Comma-separated batch sizes (e.g. 16,64,256).
        #[arg(long, default_value = "16,64,256")]
        batches: String,
        #[arg(long, default_value_t = 0)]
        prefill: usize,
        #[arg(long, default_value_t = 0)]
        seed: u64,
        #[command(flatten)]
        fri: FriArgs,
        /// Proving PCS/transcript hash. `all` runs every suite.
        #[arg(long, value_enum, default_value_t = HashArg::Poseidon2)]
        hash: HashArg,
    },
}

/// FRI knobs shared by `round` and `perf`.
#[derive(clap::Args, Debug)]
struct FriArgs {
    /// FRI log_blowup (LDE rate).
    #[arg(long, default_value_t = 1)]
    log_blowup: usize,
    /// FRI query count (linear in proof size + verifier work).
    #[arg(long, default_value_t = 100)]
    num_queries: usize,
    /// PoW grind bits before sampling queries.
    #[arg(long, default_value_t = 16)]
    query_pow_bits: usize,
    /// Max FRI folding arity (log2).
    #[arg(long, default_value_t = 3)]
    max_log_arity: usize,
}

impl FriArgs {
    fn to_cfg(&self) -> ProverConfig {
        ProverConfig {
            log_blowup: self.log_blowup,
            num_queries: self.num_queries,
            query_proof_of_work_bits: self.query_pow_bits,
            max_log_arity: self.max_log_arity,
            ..ProverConfig::default()
        }
    }
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum HashArg {
    Poseidon2,
    Sha256,
    Blake3,
    All,
}

impl HashArg {
    fn suites(self) -> &'static [ProvingHash] {
        match self {
            HashArg::Poseidon2 => &[ProvingHash::Poseidon2],
            HashArg::Sha256 => &[ProvingHash::Sha256],
            HashArg::Blake3 => &[ProvingHash::Blake3],
            HashArg::All => &[
                ProvingHash::Poseidon2,
                ProvingHash::Sha256,
                ProvingHash::Blake3,
            ],
        }
    }
}

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut bytes = [0u8; 32];
    rng.fill(&mut bytes);
    bytes_to_limbs(&bytes)
}

/// One measured R3 round: per-table cells + phase timings + proof size.
struct R3Metrics {
    cells: Vec<rsmt_prover::R3TableCells>,
    prove_time: Duration,
    verify_time: Duration,
    proof_bytes: usize,
}

/// Build a self-validated R3 round plan. Returns the plan and its build time.
fn build_round_plan(seed: u64, prefill: usize, batch: usize) -> (R3Plan, Duration) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    if prefill > 0 {
        let pre: Vec<KeyValue> = (0..prefill)
            .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
            .collect();
        tree.batch_insert(pre);
    }
    let old = tree.root_hash();
    let b: Vec<KeyValue> = (0..batch)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let (applied, proof) = tree.batch_insert(b);
    let new = tree.root_hash().expect("non-empty after batch");

    let t = Instant::now();
    let plan = build_r3_plan(&proof, &applied, old.as_ref(), &new).expect("build_r3_plan");
    (plan, t.elapsed())
}

/// Prove + verify one R3 round with the requested proving-hash suite, timing
/// each phase and serializing the proof for its byte size.
fn measure(plan: &R3Plan, seed: u64, cfg: &ProverConfig, hash: ProvingHash) -> R3Metrics {
    macro_rules! run {
        ($h:ty) => {{
            let t0 = Instant::now();
            let proof = prove_r3_round::<$h>(plan, seed, cfg);
            let prove_time = t0.elapsed();
            let bytes = bincode::serde::encode_to_vec(&proof, bincode::config::standard()).unwrap();
            let old_root = plan.old_root.unwrap_or_default();
            let publics =
                rsmt_air::table_ar::public_values(&old_root, &plan.new_root, plan.old_root_is_none);
            let t1 = Instant::now();
            verify_r3_round::<$h>(seed, cfg, &plan.shape, &publics, &proof).expect("verify");
            (prove_time, t1.elapsed(), bytes.len())
        }};
    }
    let (prove_time, verify_time, proof_bytes) = match hash {
        ProvingHash::Poseidon2 => run!(Poseidon2ProofHash),
        ProvingHash::Sha256 => run!(Sha256ProofHash),
        ProvingHash::Blake3 => run!(Blake3ProofHash),
    };
    R3Metrics {
        cells: r3_round_cells(plan),
        prove_time,
        verify_time,
        proof_bytes,
    }
}

impl R3Metrics {
    fn total_cells(&self) -> usize {
        self.cells.iter().map(|t| t.cells()).sum()
    }
    fn max_main_width(&self) -> usize {
        self.cells.iter().map(|t| t.main).max().unwrap_or(0)
    }
    fn b_perms(&self) -> usize {
        self.cells
            .iter()
            .find(|t| t.name == "B")
            .map_or(0, |t| t.real)
    }
}

fn print_tables(m: &R3Metrics) {
    println!(
        "  {:>2} {:>8} {:>8} {:>6} {:>5} {:>12}",
        "T", "real", "padded", "main", "prep", "cells"
    );
    let mut total = 0usize;
    let mut max_main = 0usize;
    for t in &m.cells {
        total += t.cells();
        max_main = max_main.max(t.main);
        println!(
            "  {:>2} {:>8} {:>8} {:>6} {:>5} {:>12}",
            t.name,
            t.real,
            t.padded,
            t.main,
            t.prep,
            t.cells(),
        );
    }
    println!(
        "  total cells={total} max_main_width={max_main} proof={:.1} KB",
        m.proof_bytes as f64 / 1024.0,
    );
    println!("  prove={:?} verify={:?}", m.prove_time, m.verify_time);
}

fn run_round(batch: usize, prefill: usize, seed: u64, cfg: &ProverConfig, hash: HashArg) {
    let (plan, wit) = build_round_plan(seed, prefill, batch);
    println!(
        "round: prefill={prefill} batch={batch} (ops={} L={} N={} O={}) witness={wit:?}",
        plan.shape.n_ops, plan.shape.n_leaf, plan.shape.n_join, plan.shape.n_open,
    );
    for &h in hash.suites() {
        println!("proof_hash={}", h.name());
        let m = measure(&plan, seed, cfg, h);
        print_tables(&m);
    }
}

fn run_perf(batches: &str, prefill: usize, seed: u64, cfg: &ProverConfig, hash: HashArg) {
    let sizes: Vec<usize> = batches
        .split(',')
        .map(|s| s.trim().parse().expect("batch size"))
        .collect();
    println!(
        "FRI: log_blowup={} num_queries={} query_pow_bits={} max_log_arity={} (~{} conjectured bits)",
        cfg.log_blowup,
        cfg.num_queries,
        cfg.query_proof_of_work_bits,
        cfg.max_log_arity,
        cfg.conjectured_soundness_bits(),
    );
    for &h in hash.suites() {
        println!("proof_hash={} prefill={prefill}", h.name());
        println!(
            "{:>6} {:>7} {:>7} {:>9} {:>13} {:>6} {:>7} {:>9} {:>10} {:>9}",
            "batch",
            "L",
            "N",
            "B_perms",
            "cells",
            "maxW",
            "wit_ms",
            "prove_ms",
            "verify_ms",
            "proof_KB",
        );
        for &b in &sizes {
            let (plan, wit) = build_round_plan(seed, prefill, b);
            let (n_l, n_join) = (plan.shape.n_leaf, plan.shape.n_join);
            let m = measure(&plan, seed, cfg, h);
            println!(
                "{:>6} {:>7} {:>7} {:>9} {:>13} {:>6} {:>7} {:>9} {:>10} {:>9.1}",
                b,
                n_l,
                n_join,
                m.b_perms(),
                m.total_cells(),
                m.max_main_width(),
                wit.as_millis(),
                m.prove_time.as_millis(),
                m.verify_time.as_millis(),
                m.proof_bytes as f64 / 1024.0,
            );
        }
    }
}

fn run_smt(prefill: usize, batch_size: usize, seed: u64) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();

    if prefill > 0 {
        let pre: Vec<KeyValue> = (0..prefill)
            .map(|_| (rand_key(&mut rng), Value32::new([1u8; 32])))
            .collect();
        let t = Instant::now();
        tree.batch_insert(pre);
        println!("prefilled {prefill} leaves in {:?}", t.elapsed());
    }

    let batch: Vec<KeyValue> = (0..batch_size)
        .map(|_| (rand_key(&mut rng), Value32::new([2u8; 32])))
        .collect();
    let pre_root = tree.root_hash();
    let t = Instant::now();
    let (items, proof) = tree.batch_insert(batch);
    let dt_insert = t.elapsed();
    let post_root = tree.root_hash().expect("non-empty");

    let t = Instant::now();
    verify_consistency::<Poseidon2Hasher>(&proof, pre_root.as_ref(), &post_root, &items)
        .expect("verify");
    let dt_verify = t.elapsed();

    let count = |pred: fn(&rsmt_core::Op<rsmt_hash::Digest>) -> bool| {
        proof.iter().filter(|o| pred(o)).count()
    };
    let n_l = count(|o| matches!(o, rsmt_core::Op::L));
    let n_n = count(|o| matches!(o, rsmt_core::Op::N { .. }));
    let n_s = count(|o| matches!(o, rsmt_core::Op::S(_)));
    println!(
        "batch={batch_size} inserted={} proof ops: L={n_l} N={n_n} S={n_s} total={} | insert={dt_insert:?} verify={dt_verify:?}",
        items.len(),
        proof.len(),
    );
}

fn main() {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();
    Registry::default()
        .with(env_filter)
        .with(ForestLayer::default())
        .init();

    match Cli::parse().cmd {
        Cmd::Smt {
            prefill,
            batch,
            seed,
        } => run_smt(prefill, batch, seed),
        Cmd::Round {
            batch,
            prefill,
            seed,
            fri,
            hash,
        } => run_round(batch, prefill, seed, &fri.to_cfg(), hash),
        Cmd::Perf {
            batches,
            prefill,
            seed,
            fri,
            hash,
        } => run_perf(&batches, prefill, seed, &fri.to_cfg(), hash),
    }
}
