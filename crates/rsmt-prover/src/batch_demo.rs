//! `p3-batch-stark::prove_batch` over the RSMT AIR batch.
//!
//! Demonstrates the heterogeneous-AIR enum dispatch pattern. Each
//! `StarkInstance` carries its own AIR variant, trace, public values, and
//! lookup list.

use num_bigint::BigUint;
use p3_air::symbolic::SymbolicExpressionExt;
use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch, verify_batch};
use p3_commit::PolynomialSpace;
use p3_field::Algebra;
use p3_field::PrimeCharacteristicRing;

use crate::config::ProverConfig;
use crate::proof_hash::{
    Blake3ProofHash, EF, F, Poseidon2ProofHash, ProvingHash, ProvingHashSuite, Sha256ProofHash,
};
use p3_matrix::dense::RowMajorMatrix;
use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use std::time::{Duration, Instant};

use rsmt_air::{
    RsmtAir, TABLE_C_WIDTH, TABLE_E_HEIGHT, TableAAir, TableBAir, TableCAir, TableDAir, TableEAir,
    TableFAir, table_a_mod, table_b_mod, table_c_mod, table_e_mod, table_f_mod,
};
use rsmt_core::{Tree, get_sort_key};
use rsmt_hash::{DIGEST_WIDTH, Poseidon2Hasher};
use rsmt_witness::{build_table_a, build_table_c, build_table_f};

/// Per-table sizing info captured during a batch run.
#[derive(Debug, Clone)]
pub struct TableMetric {
    pub name: &'static str,
    pub real_rows: usize,
    pub padded_height: usize,
    pub main_width: usize,
    pub prep_width: usize,
}

impl TableMetric {
    pub fn cells(&self) -> usize {
        self.padded_height * (self.main_width + self.prep_width)
    }
}

#[derive(Debug, Clone)]
pub struct BatchMetrics {
    pub prefill_size: usize,
    pub batch_size: usize,
    pub tables: Vec<TableMetric>,
    pub b_real_perms: usize,
    pub n_l: usize,
    pub n_n: usize,
    pub n_s: usize,
    pub witness_time: Duration,
    pub trace_time: Duration,
    pub prove_time: Duration,
    pub verify_time: Duration,
    pub proof_bytes: usize,
    pub proof_hash: &'static str,
}

impl BatchMetrics {
    pub fn total_cells(&self) -> usize {
        self.tables.iter().map(|t| t.cells()).sum()
    }
}

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
    let mut bytes = [0u8; 32];
    rng.fill(&mut bytes);
    BigUint::from_bytes_be(&bytes)
}

fn rand_value(rng: &mut Xoshiro256PlusPlus) -> Vec<u8> {
    let mut bytes = [0u8; 32];
    rng.fill(&mut bytes);
    bytes.to_vec()
}

/// Holds per-table mutable trace handles for tamper-test injection.
pub struct Traces<'a> {
    pub a: &'a mut RowMajorMatrix<F>,
    pub f: &'a mut RowMajorMatrix<F>,
    pub b: &'a mut RowMajorMatrix<F>,
    pub c: &'a mut RowMajorMatrix<F>,
    pub e: &'a mut RowMajorMatrix<F>,
    pub d: &'a mut RowMajorMatrix<F>,
}

/// Prove and verify the six RSMT AIRs together via `prove_batch`.
pub fn prove_and_verify_all_tables(seed: u64, batch_size: usize) {
    prove_and_verify_inner(seed, batch_size, |_| {}).expect("verify_batch");
}

/// Same as `prove_and_verify_with_metrics`, but with caller-supplied FRI knobs.
pub fn prove_and_verify_with_metrics_cfg(
    seed: u64,
    batch_size: usize,
    cfg: &ProverConfig,
) -> BatchMetrics {
    prove_and_verify_with_metrics_cfg_for::<Poseidon2ProofHash>(seed, batch_size, cfg)
}

pub fn prove_and_verify_with_metrics_cfg_for<H: ProvingHashSuite>(
    seed: u64,
    batch_size: usize,
    cfg: &ProverConfig,
) -> BatchMetrics
where
    BatchProof<H::Config>: serde::Serialize,
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
{
    let (res, m) = prove_and_verify_collect::<H>(seed, 0, batch_size, cfg, |_| {});
    res.expect("verify_batch");
    m
}

pub fn prove_and_verify_with_metrics_cfg_for_prefill<H: ProvingHashSuite>(
    seed: u64,
    prefill_size: usize,
    batch_size: usize,
    cfg: &ProverConfig,
) -> BatchMetrics
where
    BatchProof<H::Config>: serde::Serialize,
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
{
    let (res, m) = prove_and_verify_collect::<H>(seed, prefill_size, batch_size, cfg, |_| {});
    res.expect("verify_batch");
    m
}

pub fn prove_and_verify_with_metrics_cfg_hash(
    seed: u64,
    batch_size: usize,
    cfg: &ProverConfig,
    hash: ProvingHash,
) -> BatchMetrics {
    prove_and_verify_with_metrics_cfg_hash_prefill(seed, 0, batch_size, cfg, hash)
}

pub fn prove_and_verify_with_metrics_cfg_hash_prefill(
    seed: u64,
    prefill_size: usize,
    batch_size: usize,
    cfg: &ProverConfig,
    hash: ProvingHash,
) -> BatchMetrics {
    match hash {
        ProvingHash::Poseidon2 => {
            prove_and_verify_with_metrics_cfg_for_prefill::<Poseidon2ProofHash>(
                seed,
                prefill_size,
                batch_size,
                cfg,
            )
        }
        ProvingHash::Sha256 => prove_and_verify_with_metrics_cfg_for_prefill::<Sha256ProofHash>(
            seed,
            prefill_size,
            batch_size,
            cfg,
        ),
        ProvingHash::Blake3 => prove_and_verify_with_metrics_cfg_for_prefill::<Blake3ProofHash>(
            seed,
            prefill_size,
            batch_size,
            cfg,
        ),
    }
}

pub fn prove_and_verify_a_plus_f(seed: u64, batch_size: usize) {
    prove_and_verify_all_tables(seed, batch_size);
}

/// Tamper a Table C final-state tail limb that only Bus 2 should protect.
pub fn prove_with_tampered_poseidon_tail(seed: u64, batch_size: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch_size, |t| {
        use p3_field::PrimeCharacteristicRing;

        // Row 2 is the final sponge step for the first leaf. Its last
        // state_out limb is not part of the digest and is not read by the next
        // C row, but it is part of the full Poseidon2 lookup tuple.
        let idx = 2 * TABLE_C_WIDTH + (TABLE_C_WIDTH - 1);
        t.c.values[idx] += F::ONE;
    })
}

/// Prove and report metrics. Used by the bench CLI.
pub fn prove_and_verify_with_metrics(seed: u64, batch_size: usize) -> BatchMetrics {
    prove_and_verify_with_metrics_cfg_for::<Poseidon2ProofHash>(
        seed,
        batch_size,
        &ProverConfig::default(),
    )
}

pub fn prove_and_verify_inner(
    seed: u64,
    batch_size: usize,
    tamper: impl FnOnce(&mut Traces<'_>),
) -> Result<(), ()> {
    prove_and_verify_collect::<Poseidon2ProofHash>(
        seed,
        0,
        batch_size,
        &ProverConfig::default(),
        tamper,
    )
    .0
}

fn prove_and_verify_collect<H: ProvingHashSuite>(
    seed: u64,
    prefill_size: usize,
    batch_size: usize,
    cfg: &ProverConfig,
    tamper: impl FnOnce(&mut Traces<'_>),
) -> (Result<(), ()>, BatchMetrics)
where
    BatchProof<H::Config>: serde::Serialize,
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
{
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();

    if prefill_size > 0 {
        let prefill: Vec<_> = (0..prefill_size)
            .map(|_| (rand_key(&mut rng), rand_value(&mut rng)))
            .collect();
        tree.batch_insert(prefill);
    }

    let batch: Vec<_> = (0..batch_size)
        .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
        .collect();
    let pre_root = tree.root_hash();
    let (items, proof) = tree.batch_insert(batch);
    let post_root = tree.root_hash().expect("post root");
    let mut sorted = items;
    sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

    let witness_start = Instant::now();
    // A, F, C witnesses are independent; build them in parallel. B's inputs
    // join C and F, so they run after.
    let (a_rows, (f_rows, c_rows)) = rayon::join(
        || build_table_a::<Poseidon2Hasher>(&proof, &sorted),
        || {
            rayon::join(
                || build_table_f::<Poseidon2Hasher>(&proof, &sorted),
                || build_table_c(&sorted),
            )
        },
    );
    let b_inputs = table_b_mod::collect_poseidon2_inputs(&c_rows, &f_rows);
    let witness_time = witness_start.elapsed();

    let trace_start = Instant::now();
    // All five trace materializations are independent; run in parallel.
    // Table B's inner trace generation is itself parallel via Plonky3.
    let d_height = sorted.len().next_power_of_two().max(2);
    let n_depths: Vec<u8> = a_rows.iter().filter(|r| r.is_n).map(|r| r.depth).collect();

    let ((a_built, f_built), (c_built, (b_built, (d_built, e_built)))) = rayon::join(
        || {
            rayon::join(
                || table_a_mod::build_trace_babybear(&a_rows),
                || table_f_mod::build_trace_babybear(&f_rows),
            )
        },
        || {
            rayon::join(
                || table_c_mod::build_trace_babybear(&c_rows),
                || {
                    rayon::join(
                        || table_b_mod::build_trace_babybear(&b_inputs),
                        || {
                            rayon::join(
                                || RowMajorMatrix::<F>::new(vec![F::ZERO; d_height], 1),
                                || table_e_mod::build_main_babybear(n_depths),
                            )
                        },
                    )
                },
            )
        },
    );
    let (mut a_trace, a_real, a_height) = a_built;
    let (mut f_trace, f_real, f_height) = f_built;
    let (mut c_trace, c_real, c_height) = c_built;
    let (mut b_trace, b_real, b_height) = b_built;
    let mut d_trace: RowMajorMatrix<F> = d_built;
    let mut e_trace = e_built;
    let trace_time = trace_start.elapsed();

    {
        let mut t = Traces {
            a: &mut a_trace,
            f: &mut f_trace,
            b: &mut b_trace,
            c: &mut c_trace,
            e: &mut e_trace,
            d: &mut d_trace,
        };
        tamper(&mut t);
    }

    let n_l = a_rows.iter().filter(|r| r.is_l).count();
    let n_n = a_rows.iter().filter(|r| r.is_n).count();
    let n_s = a_rows.iter().filter(|r| r.is_s).count();

    let air_a = RsmtAir::A(TableAAir::new(a_height, a_real));
    let air_f = RsmtAir::F(TableFAir::new(f_height, f_real));
    let air_b = RsmtAir::B(TableBAir::new(b_height, b_real));
    let air_e = RsmtAir::E(TableEAir::new());
    let air_c = RsmtAir::C(TableCAir::new(c_height, c_real));
    let air_d = RsmtAir::D(TableDAir::for_batch(&sorted));
    let _ = TABLE_E_HEIGHT;
    let _ = d_height;

    let mut publics_a = Vec::with_capacity(2 * DIGEST_WIDTH);
    let zero = [F::ZERO; DIGEST_WIDTH];
    for v in pre_root.unwrap_or(zero) {
        publics_a.push(v);
    }
    for v in post_root {
        publics_a.push(v);
    }
    let publics_f: Vec<F> = vec![];
    let publics_b: Vec<F> = vec![];
    let publics_e: Vec<F> = vec![];
    let publics_c: Vec<F> = vec![];
    let publics_d: Vec<F> = vec![];

    let config = H::build_config(seed, cfg);

    // Build instances with empty lookups so we can call ProverData::from_instances,
    // which deduces and populates `common.lookups` from each AIR's `get_lookups`.
    let instances0 = vec![
        StarkInstance {
            air: &air_a,
            trace: &a_trace,
            public_values: publics_a.clone(),
            lookups: vec![],
        },
        StarkInstance {
            air: &air_f,
            trace: &f_trace,
            public_values: publics_f.clone(),
            lookups: vec![],
        },
        StarkInstance {
            air: &air_b,
            trace: &b_trace,
            public_values: publics_b.clone(),
            lookups: vec![],
        },
        StarkInstance {
            air: &air_e,
            trace: &e_trace,
            public_values: publics_e.clone(),
            lookups: vec![],
        },
        StarkInstance {
            air: &air_c,
            trace: &c_trace,
            public_values: publics_c.clone(),
            lookups: vec![],
        },
        StarkInstance {
            air: &air_d,
            trace: &d_trace,
            public_values: publics_d.clone(),
            lookups: vec![],
        },
    ];
    let prover_data = ProverData::from_instances(&config, &instances0);

    let traces_refs: Vec<&_> = vec![&a_trace, &f_trace, &b_trace, &e_trace, &c_trace, &d_trace];
    let airs_slice = vec![
        air_a.clone(),
        air_f.clone(),
        air_b.clone(),
        air_e.clone(),
        air_c.clone(),
        air_d.clone(),
    ];
    let pvs_in = vec![
        publics_a.clone(),
        publics_f.clone(),
        publics_b.clone(),
        publics_e.clone(),
        publics_c.clone(),
        publics_d.clone(),
    ];
    let instances =
        StarkInstance::new_multiple(&airs_slice, &traces_refs, &pvs_in, &prover_data.common);

    let prove_start = Instant::now();
    let proof_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_batch(&config, &instances, &prover_data)
    }));
    let prove_time = prove_start.elapsed();

    let tables = vec![
        TableMetric {
            name: "A",
            real_rows: a_real,
            padded_height: a_height,
            main_width: a_trace.width,
            prep_width: rsmt_air::TABLE_A_PREP_WIDTH,
        },
        TableMetric {
            name: "F",
            real_rows: f_real,
            padded_height: f_height,
            main_width: f_trace.width,
            prep_width: rsmt_air::TABLE_F_PREP_WIDTH,
        },
        TableMetric {
            name: "B",
            real_rows: b_real,
            padded_height: b_height,
            main_width: b_trace.width,
            prep_width: rsmt_air::P2_VECTOR_LEN,
        },
        TableMetric {
            name: "C",
            real_rows: c_real,
            padded_height: c_height,
            main_width: c_trace.width,
            prep_width: rsmt_air::TABLE_C_PREP_WIDTH,
        },
        TableMetric {
            name: "D",
            real_rows: sorted.len(),
            padded_height: d_height,
            main_width: d_trace.width,
            prep_width: rsmt_air::TABLE_D_PREP_WIDTH,
        },
        TableMetric {
            name: "E",
            real_rows: 256,
            padded_height: 256,
            main_width: e_trace.width,
            prep_width: 1,
        },
    ];

    let mut metrics = BatchMetrics {
        prefill_size,
        batch_size,
        tables,
        b_real_perms: b_real,
        n_l,
        n_n,
        n_s,
        witness_time,
        trace_time,
        prove_time,
        verify_time: Duration::ZERO,
        proof_bytes: 0,
        proof_hash: H::NAME,
    };

    let proof = match proof_res {
        Ok(p) => p,
        Err(_) => return (Err(()), metrics),
    };

    metrics.proof_bytes = bincode::serde::encode_to_vec(&proof, bincode::config::standard())
        .map(|v| v.len())
        .unwrap_or(0);

    // Verifier-side AIRs: TableD is shape-only (no batch data). The batch
    // lives in the global preprocessed commitment inside `prover_data.common`.
    let air_d_verifier = RsmtAir::D(TableDAir::shape_only(d_height));
    let airs = vec![air_a, air_f, air_b, air_e, air_c, air_d_verifier];
    let pvs = vec![
        publics_a, publics_f, publics_b, publics_e, publics_c, publics_d,
    ];
    let verify_start = Instant::now();
    let res = verify_batch(&config, &airs, &proof, &pvs, &prover_data.common).map_err(|e| {
        eprintln!("verify_batch error: {:?}", e);
    });
    metrics.verify_time = verify_start.elapsed();
    (res, metrics)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn batch_all_tables_proves_and_verifies() {
        prove_and_verify_all_tables(7, 16);
    }

    #[test]
    fn batch_all_tables_proves_and_verifies_sha256() {
        let metrics = prove_and_verify_with_metrics_cfg_for::<Sha256ProofHash>(
            7,
            16,
            &ProverConfig::default(),
        );
        assert_eq!(metrics.proof_hash, Sha256ProofHash::NAME);
    }

    #[test]
    fn batch_all_tables_proves_and_verifies_blake3() {
        let metrics = prove_and_verify_with_metrics_cfg_for::<Blake3ProofHash>(
            7,
            16,
            &ProverConfig::default(),
        );
        assert_eq!(metrics.proof_hash, Blake3ProofHash::NAME);
    }

    #[test]
    fn tampered_poseidon_tail_is_rejected() {
        assert!(prove_with_tampered_poseidon_tail(7, 16).is_err());
    }
}
