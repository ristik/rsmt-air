//! `rsmt-bench` — CLI entry point.
//!
//! Today exposes two subcommands:
//! - `smt`: build a tree, apply a batch, verify the consistency proof on the CPU.
//! - `poseidon2`: end-to-end FRI proof of a batch of Poseidon2 permutations.

use std::time::Instant;

use clap::{Parser, Subcommand, ValueEnum};
use num_bigint::BigUint;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;
use tracing_forest::ForestLayer;
use tracing_forest::util::LevelFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

use rsmt_core::{Tree, verify_consistency};
use rsmt_hash::Poseidon2Hasher;
use rsmt_prover::batch_demo::{
    prove_and_verify_with_metrics_cfg_hash, prove_and_verify_with_metrics_cfg_hash_prefill,
};
use rsmt_prover::config::ProverConfig;
use rsmt_prover::poseidon2_demo::{P2_VECTOR_LEN, prove_and_verify_poseidon2};
use rsmt_prover::proof_hash::ProvingHash;
use rsmt_prover::table_a_demo::prove_and_verify_table_a;
use rsmt_prover::table_f_demo::prove_and_verify_table_f;

#[derive(Parser, Debug)]
#[command(version, about = "RSMT3 AIR proof-of-concept benchmarks")]
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
    /// End-to-end Poseidon2 proof over BabyBear via TwoAdicFriPcs.
    Poseidon2 {
        /// Number of permutations (must be VECTOR_LEN × pow-of-2).
        #[arg(long, default_value_t = 1024)]
        num_hashes: usize,
    },
    /// FRI prove+verify Table A in isolation.
    TableA {
        #[arg(long, default_value_t = 64)]
        batch: usize,
        #[arg(long, default_value_t = 0)]
        seed: u64,
    },
    /// FRI prove+verify Table F in isolation.
    TableF {
        #[arg(long, default_value_t = 64)]
        batch: usize,
        #[arg(long, default_value_t = 0)]
        seed: u64,
    },
    /// `prove_batch` over all six AIRs with LogUp buses.
    Batch {
        #[arg(long, default_value_t = 16)]
        batch: usize,
        #[arg(long, default_value_t = 0)]
        seed: u64,
        #[arg(long, value_enum, default_value_t = ProofHashArg::Poseidon2)]
        hash: ProofHashArg,
    },
    /// Sweep batch sizes through `prove_batch` and report per-table metrics.
    Perf {
        /// Comma-separated batch sizes (e.g. 16,64,256,1024).
        #[arg(long, default_value = "16,64,256")]
        batches: String,
        /// Pre-insert this many random leaves before proving each measured batch.
        #[arg(long, default_value_t = 0)]
        prefill: usize,
        #[arg(long, default_value_t = 0)]
        seed: u64,
        /// FRI log_blowup (LDE rate). Larger → bigger LDE, fewer queries
        /// for the same soundness, smaller proof.
        #[arg(long, default_value_t = 1)]
        log_blowup: usize,
        /// FRI query count. Linear in proof size and verifier work.
        #[arg(long, default_value_t = 100)]
        num_queries: usize,
        /// PoW grind bits before sampling queries. Shifts work to prover.
        #[arg(long, default_value_t = 16)]
        query_pow_bits: usize,
        /// Max FRI folding arity (log2). 1 = binary folding.
        #[arg(long, default_value_t = 3)]
        max_log_arity: usize,
        /// Proving PCS/transcript hash. `all` runs both suites.
        #[arg(long, value_enum, default_value_t = PerfHashArg::Poseidon2)]
        hash: PerfHashArg,
    },
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum ProofHashArg {
    Poseidon2,
    Sha256,
    Blake3,
}

impl From<ProofHashArg> for ProvingHash {
    fn from(value: ProofHashArg) -> Self {
        match value {
            ProofHashArg::Poseidon2 => Self::Poseidon2,
            ProofHashArg::Sha256 => Self::Sha256,
            ProofHashArg::Blake3 => Self::Blake3,
        }
    }
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum PerfHashArg {
    Poseidon2,
    Sha256,
    Blake3,
    All,
}

fn run_perf(batches: &str, prefill: usize, seed: u64, cfg: &ProverConfig, hash_arg: PerfHashArg) {
    let sizes: Vec<usize> = batches
        .split(',')
        .map(|s| s.trim().parse().expect("batch size"))
        .collect();
    let hashes: &[ProvingHash] = match hash_arg {
        PerfHashArg::Poseidon2 => &[ProvingHash::Poseidon2],
        PerfHashArg::Sha256 => &[ProvingHash::Sha256],
        PerfHashArg::Blake3 => &[ProvingHash::Blake3],
        PerfHashArg::All => &[
            ProvingHash::Poseidon2,
            ProvingHash::Sha256,
            ProvingHash::Blake3,
        ],
    };

    for &hash in hashes {
        println!("proof_hash={}", hash.name());
        println!("prefill={prefill}");
        println!(
            "FRI: log_blowup={} num_queries={} query_pow_bits={} max_log_arity={} (~{} conjectured soundness bits)",
            cfg.log_blowup,
            cfg.num_queries,
            cfg.query_proof_of_work_bits,
            cfg.max_log_arity,
            cfg.conjectured_soundness_bits(),
        );
        println!(
            "{:>5} {:>8} {:>8} {:>10} {:>12} {:>10} {:>9} {:>9} {:>10} {:>10}",
            "batch",
            "L_ops",
            "N_ops",
            "B_perms",
            "cells",
            "wit_ms",
            "trace_ms",
            "prove_ms",
            "verify_ms",
            "proof_KB",
        );
        for &b in &sizes {
            let m = prove_and_verify_with_metrics_cfg_hash_prefill(seed, prefill, b, cfg, hash);
            println!(
                "{:>5} {:>8} {:>8} {:>10} {:>12} {:>10} {:>9} {:>9} {:>10} {:>10.1}",
                m.batch_size,
                m.n_l,
                m.n_n,
                m.b_real_perms,
                m.total_cells(),
                m.witness_time.as_millis(),
                m.trace_time.as_millis(),
                m.prove_time.as_millis(),
                m.verify_time.as_millis(),
                m.proof_bytes as f64 / 1024.0,
            );
            println!("  per-table (name real/padded main+prep cells):");
            for t in &m.tables {
                println!(
                    "    {:>2}: {:>6}/{:<6} {:>3}+{:<2} = {:>10}",
                    t.name,
                    t.real_rows,
                    t.padded_height,
                    t.main_width,
                    t.prep_width,
                    t.cells(),
                );
            }
        }
    }
}

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
    let mut bytes = [0u8; 32];
    rng.fill(&mut bytes);
    BigUint::from_bytes_be(&bytes)
}

fn run_smt(prefill: usize, batch_size: usize, seed: u64) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();

    if prefill > 0 {
        let pre: Vec<_> = (0..prefill)
            .map(|_| (rand_key(&mut rng), vec![0u8; 32]))
            .collect();
        let t = Instant::now();
        tree.batch_insert(pre);
        println!("prefilled {} leaves in {:?}", prefill, t.elapsed());
    }

    let batch: Vec<_> = (0..batch_size)
        .map(|_| (rand_key(&mut rng), vec![0u8; 32]))
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

    let n_l = proof
        .iter()
        .filter(|o| matches!(o, rsmt_core::Op::L))
        .count();
    let n_n = proof
        .iter()
        .filter(|o| matches!(o, rsmt_core::Op::N(_)))
        .count();
    let n_s = proof
        .iter()
        .filter(|o| matches!(o, rsmt_core::Op::S(_)))
        .count();
    println!(
        "batch={} inserted={} proof ops: L={} N={} S={} total={} | insert={:?} verify={:?}",
        batch_size,
        items.len(),
        n_l,
        n_n,
        n_s,
        proof.len(),
        dt_insert,
        dt_verify
    );
}

fn run_poseidon2(num_hashes: usize) {
    assert!(
        num_hashes.is_multiple_of(P2_VECTOR_LEN) && (num_hashes / P2_VECTOR_LEN).is_power_of_two(),
        "num_hashes must be VECTOR_LEN ({P2_VECTOR_LEN}) × power of 2"
    );
    let t = Instant::now();
    prove_and_verify_poseidon2(num_hashes);
    println!(
        "Poseidon2 proof+verify for {num_hashes} perms: {:?}",
        t.elapsed()
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
        Cmd::Poseidon2 { num_hashes } => run_poseidon2(num_hashes),
        Cmd::TableA { batch, seed } => {
            let t = Instant::now();
            prove_and_verify_table_a(seed, batch);
            println!(
                "Table A FRI prove+verify (batch={batch}): {:?}",
                t.elapsed()
            );
        }
        Cmd::TableF { batch, seed } => {
            let t = Instant::now();
            prove_and_verify_table_f(seed, batch);
            println!(
                "Table F FRI prove+verify (batch={batch}): {:?}",
                t.elapsed()
            );
        }
        Cmd::Batch { batch, seed, hash } => {
            let t = Instant::now();
            let cfg = ProverConfig::default();
            let _ = prove_and_verify_with_metrics_cfg_hash(seed, batch, &cfg, hash.into());
            println!(
                "Batch all AIRs prove+verify (batch={batch}, hash={}): {:?}",
                ProvingHash::from(hash).name(),
                t.elapsed()
            );
        }
        Cmd::Perf {
            batches,
            prefill,
            seed,
            log_blowup,
            num_queries,
            query_pow_bits,
            max_log_arity,
            hash,
        } => {
            let cfg = ProverConfig {
                log_blowup,
                num_queries,
                query_proof_of_work_bits: query_pow_bits,
                max_log_arity,
                ..ProverConfig::default()
            };
            run_perf(&batches, prefill, seed, &cfg, hash);
        }
    }
}
