//! End-to-end round proving (DEVPLAN M4).
//!
//! `prove_and_verify_round` turns a `TracePlan` into a batch STARK over the
//! seven table AIRs sharing one preprocessed/main commitment, then verifies it
//! against the public `(old_root, new_root)` and the per-table shape. Buses are
//! wired table-by-table; with the current bus-free `LookupAir` defaults this
//! proves each table's **local** constraints through the real FRI stack.

use p3_air::symbolic::SymbolicExpressionExt;
use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch, verify_batch};
use p3_commit::PolynomialSpace;
use p3_field::Algebra;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_air::{
    RsmtAir, TableAAir, TableBAir, TableCAir, TableDAir, TableFAir, TablePAir, TableRAir, table_a,
    table_b, table_c, table_d, table_f, table_p, table_r,
};
use rsmt_witness::TracePlan;

use crate::config::ProverConfig;
use crate::proof_hash::{EF, F, ProvingHashSuite};

/// Per-table real-row shape — part of the public statement, fixing every
/// verifier-side AIR (all preprocessed traces except Table D's committed batch).
#[derive(Clone, Debug)]
pub struct RoundShape {
    pub a_height: usize,
    pub a_real: usize,
    pub b_height: usize,
    pub b_real: usize,
    pub b_modes: Vec<bool>,
    pub c_height: usize,
    pub c_real: usize,
    pub c_batch_rows: usize,
    pub d_height: usize,
    pub f_height: usize,
    pub f_njoin: usize,
    pub f_nopen: usize,
}

fn shape_airs(s: &RoundShape, d: TableDAir) -> Vec<RsmtAir> {
    vec![
        RsmtAir::A(TableAAir::new(s.a_height, s.a_real)),
        RsmtAir::B(TableBAir::new(s.b_height, s.b_real, s.b_modes.clone())),
        RsmtAir::C(TableCAir::new(s.c_height, s.c_real, s.c_batch_rows)),
        RsmtAir::D(d),
        RsmtAir::R(TableRAir::default()),
        RsmtAir::F(TableFAir::new(s.f_height, s.f_njoin, s.f_nopen)),
        RsmtAir::P(TablePAir::default()),
    ]
}

fn public_vals(publics_a: &[F]) -> Vec<Vec<F>> {
    vec![
        publics_a.to_vec(),
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
    ]
}

/// Mutable handle on the seven per-round main traces, handed to a tamper hook
/// (M5, verification-plan §4) after generation but before the commitment so an
/// adversarial mutation must be caught by constraints or LogUp balance.
pub struct RoundTraces<'a> {
    pub a: &'a mut RowMajorMatrix<F>,
    pub b: &'a mut RowMajorMatrix<F>,
    pub c: &'a mut RowMajorMatrix<F>,
    pub d: &'a mut RowMajorMatrix<F>,
    pub r: &'a mut RowMajorMatrix<F>,
    pub f: &'a mut RowMajorMatrix<F>,
    pub p: &'a mut RowMajorMatrix<F>,
}

/// Prove all seven tables for a round and verify the proof (single process).
pub fn prove_and_verify_round<H: ProvingHashSuite>(
    plan: &TracePlan,
    seed: u64,
    cfg: &ProverConfig,
) -> Result<(), String>
where
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    BatchProof<H::Config>: Sized,
{
    prove_and_verify_round_with::<H>(plan, seed, cfg, |_| {})
}

/// Like [`prove_and_verify_round`] but applies `tamper` to the freshly-built
/// main traces before committing. With an identity hook this is exactly the
/// honest path; the M5 sweep passes mutations and asserts `Err`.
pub fn prove_and_verify_round_with<H: ProvingHashSuite>(
    plan: &TracePlan,
    seed: u64,
    cfg: &ProverConfig,
    tamper: impl FnOnce(&mut RoundTraces<'_>),
) -> Result<(), String>
where
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    BatchProof<H::Config>: Sized,
{
    // -- traces from the plan --
    let (mut a, a_real, a_height) = table_a::build_trace(&plan.a_rows);
    let b_inputs = table_b::collect_inputs(plan);
    let b_modes = table_b::collect_modes(plan);
    let (mut b, b_real, b_height) = table_b::build_trace(&b_inputs);
    let (mut c, c_real, c_height, c_batch_rows) = table_c::build_trace(plan);
    let (mut f, f_njoin, f_nopen, f_height) = table_f::build_trace(plan);
    let d_air = TableDAir::for_rows(&plan.d_rows);
    let d_height = d_air.padded_height;
    let mut d = table_d::build_main(d_height);
    let mut e = table_r::build_main(&plan.r_mults);
    let mut p = table_p::build_main(&plan.p_mults);

    // M5 tamper hook (identity for the honest path).
    {
        let mut handle = RoundTraces {
            a: &mut a,
            b: &mut b,
            c: &mut c,
            d: &mut d,
            r: &mut e,
            f: &mut f,
            p: &mut p,
        };
        tamper(&mut handle);
    }

    let shape = RoundShape {
        a_height,
        a_real,
        b_height,
        b_real,
        b_modes,
        c_height,
        c_real,
        c_batch_rows,
        d_height,
        f_height,
        f_njoin,
        f_nopen,
    };
    let publics_a = table_a::public_values(&plan.publics);
    let pv = public_vals(&publics_a);

    let config = H::build_config(seed, cfg);
    let airs = shape_airs(&shape, d_air.clone());
    let traces = [&a, &b, &c, &d, &e, &f, &p];

    let instances0: Vec<StarkInstance<'_, H::Config, RsmtAir>> = airs
        .iter()
        .zip(traces.iter())
        .zip(pv.iter())
        .map(|((air, trace), public_values)| StarkInstance {
            air,
            trace,
            public_values: public_values.clone(),
            lookups: vec![],
        })
        .collect();
    let prover_data = ProverData::from_instances(&config, &instances0);

    let traces_refs: Vec<&RowMajorMatrix<F>> = traces.to_vec();
    let instances = StarkInstance::new_multiple(&airs, &traces_refs, &pv, &prover_data.common);
    let proof = prove_batch(&config, &instances, &prover_data);

    // Verifier side: Table D shape-only (batch lives in the shared commitment).
    let airs_v = shape_airs(&shape, TableDAir::shape_only(d_height));
    verify_batch(&config, &airs_v, &proof, &pv, &prover_data.common).map_err(|e| format!("{e:?}"))
}

// ---------------------------------------------------------------------------
// Metrics (M6)
// ---------------------------------------------------------------------------

/// Per-table sizing captured during a measured round.
#[derive(Debug, Clone)]
pub struct TableMetric {
    pub name: &'static str,
    pub real_rows: usize,
    pub padded_height: usize,
    pub main_width: usize,
    pub prep_width: usize,
}

impl TableMetric {
    /// Committed cells: padded rows × (main + preprocessed) columns.
    pub fn cells(&self) -> usize {
        self.padded_height * (self.main_width + self.prep_width)
    }
}

/// One measured round: per-table sizing, timings, and proof size.
#[derive(Debug, Clone)]
pub struct RoundMetrics {
    pub tables: Vec<TableMetric>,
    pub b_real_perms: usize,
    pub n_l: usize,
    pub n_join: usize,
    pub n_open: usize,
    pub n_s: usize,
    pub trace_time: std::time::Duration,
    pub prove_time: std::time::Duration,
    pub verify_time: std::time::Duration,
    pub proof_bytes: usize,
}

impl RoundMetrics {
    pub fn total_cells(&self) -> usize {
        self.tables.iter().map(TableMetric::cells).sum()
    }
    /// Widest main trace — the column-budget headline.
    pub fn max_main_width(&self) -> usize {
        self.tables.iter().map(|t| t.main_width).max().unwrap_or(0)
    }
}

/// Prove+verify one round like [`prove_and_verify_round`], additionally timing
/// trace generation / prove / verify, serializing the proof for its byte size,
/// and returning the per-table shape breakdown (M6). Errors on verification
/// failure.
pub fn prove_and_verify_round_metrics<H: ProvingHashSuite>(
    plan: &TracePlan,
    seed: u64,
    cfg: &ProverConfig,
) -> Result<RoundMetrics, String>
where
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    BatchProof<H::Config>: Sized,
{
    use std::time::Instant;

    let trace_start = Instant::now();
    let (a, a_real, a_height) = table_a::build_trace(&plan.a_rows);
    let b_inputs = table_b::collect_inputs(plan);
    let b_modes = table_b::collect_modes(plan);
    let (b, b_real, b_height) = table_b::build_trace(&b_inputs);
    let (c, c_real, c_height, c_batch_rows) = table_c::build_trace(plan);
    let (f, f_njoin, f_nopen, f_height) = table_f::build_trace(plan);
    let d_air = TableDAir::for_rows(&plan.d_rows);
    let d_height = d_air.padded_height;
    let d = table_d::build_main(d_height);
    let r = table_r::build_main(&plan.r_mults);
    let p = table_p::build_main(&plan.p_mults);
    let trace_time = trace_start.elapsed();

    let shape = RoundShape {
        a_height,
        a_real,
        b_height,
        b_real,
        b_modes,
        c_height,
        c_real,
        c_batch_rows,
        d_height,
        f_height,
        f_njoin,
        f_nopen,
    };
    let publics_a = table_a::public_values(&plan.publics);
    let pv = public_vals(&publics_a);

    let config = H::build_config(seed, cfg);
    let airs = shape_airs(&shape, d_air.clone());
    let traces = [&a, &b, &c, &d, &r, &f, &p];

    let instances0: Vec<StarkInstance<'_, H::Config, RsmtAir>> = airs
        .iter()
        .zip(traces.iter())
        .zip(pv.iter())
        .map(|((air, trace), public_values)| StarkInstance {
            air,
            trace,
            public_values: public_values.clone(),
            lookups: vec![],
        })
        .collect();
    let prover_data = ProverData::from_instances(&config, &instances0);
    let traces_refs: Vec<&RowMajorMatrix<F>> = traces.to_vec();
    let instances = StarkInstance::new_multiple(&airs, &traces_refs, &pv, &prover_data.common);

    let prove_start = Instant::now();
    let proof = prove_batch(&config, &instances, &prover_data);
    let prove_time = prove_start.elapsed();

    let proof_bytes = bincode::serde::encode_to_vec(&proof, bincode::config::standard())
        .map(|v| v.len())
        .unwrap_or(0);

    let airs_v = shape_airs(&shape, TableDAir::shape_only(d_height));
    let verify_start = Instant::now();
    verify_batch(&config, &airs_v, &proof, &pv, &prover_data.common)
        .map_err(|e| format!("{e:?}"))?;
    let verify_time = verify_start.elapsed();

    let tables = vec![
        TableMetric {
            name: "A",
            real_rows: a_real,
            padded_height: a_height,
            main_width: a.width,
            prep_width: table_a::TABLE_A_PREP_WIDTH,
        },
        TableMetric {
            name: "B",
            real_rows: b_real,
            padded_height: b_height,
            main_width: b.width,
            prep_width: table_b::P2_PREP_WIDTH,
        },
        TableMetric {
            name: "C",
            real_rows: c_real,
            padded_height: c_height,
            main_width: c.width,
            prep_width: table_c::TABLE_C_PREP_WIDTH,
        },
        TableMetric {
            name: "D",
            real_rows: plan.d_rows.len(),
            padded_height: d_height,
            main_width: d.width,
            prep_width: table_d::TABLE_D_PREP_WIDTH,
        },
        TableMetric {
            name: "R",
            real_rows: rsmt_air::table_r::TABLE_R_REAL,
            padded_height: r.height(),
            main_width: r.width,
            prep_width: table_r::TABLE_R_PREP_WIDTH,
        },
        TableMetric {
            name: "F",
            real_rows: f_njoin + f_nopen,
            padded_height: f_height,
            main_width: f.width,
            prep_width: table_f::TABLE_F_PREP_WIDTH,
        },
        TableMetric {
            name: "P",
            real_rows: rsmt_air::table_p::TABLE_P_REAL,
            padded_height: p.height(),
            main_width: p.width,
            prep_width: table_p::TABLE_P_PREP_WIDTH,
        },
    ];

    Ok(RoundMetrics {
        tables,
        b_real_perms: b_real,
        n_l: plan.shape.n_l,
        n_join: f_njoin,
        n_open: f_nopen,
        n_s: plan.shape.n_s,
        trace_time,
        prove_time,
        verify_time,
        proof_bytes,
    })
}
