//! End-to-end R3 round proving (M7): build the seven R3 traces
//! (`A/B/L/J/O/R/P`) from an [`R3Plan`] and prove+verify them as one batch STARK
//! with **full cross-table bus balance**. This is the test that validates every
//! R3 bus tuple (leaf/parent/tree/p2ff/p2term/range/pow2) end to end.
//!
//! Table B consumes the occurrence-correct [`PermutationPlan`] as a single
//! `feed_forward ‖ terminal` segment, with per-perm modes derived from the
//! scalar counts `(n_ff, n_term)` — no `Vec<bool>` in the public shape.

use p3_air::symbolic::SymbolicExpressionExt;
use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch, verify_batch};
use p3_commit::PolynomialSpace;
use p3_field::Algebra;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_air::table_ar::TableArAir;
use rsmt_air::table_j::TableJAir;
use rsmt_air::table_l::TableLAir;
use rsmt_air::table_o::TableOAir;
use rsmt_air::{
    R3Air, TableBAir, TablePAir, TableRAir, table_ar, table_b, table_j, table_l, table_o, table_p,
    table_r,
};
use rsmt_hash::State;
use rsmt_witness::r3build::R3Plan;

use crate::config::ProverConfig;
use crate::proof_hash::{EF, F, ProvingHashSuite};

/// The public [`rsmt_protocol::RoundShape`] (scalar counts only) for a plan. The
/// verifier reconstructs the *same* value from the public inputs and runs
/// [`rsmt_protocol::RoundShape::validate`] before accepting.
pub fn round_shape(plan: &R3Plan) -> rsmt_protocol::RoundShape {
    let s = &plan.shape;
    rsmt_protocol::RoundShape {
        n_ops: s.n_ops,
        n_leaf: s.n_leaf,
        n_join: s.n_join,
        n_open: s.n_open,
        n_b11: s.n_b11,
        n_p2ff: s.n_p2ff,
        n_p2term: s.n_p2term,
    }
}

/// Mutable handle on the seven R3 main traces, handed to a tamper hook (M8)
/// after generation but before the commitment, so an adversarial mutation must
/// be caught by a local constraint or a LogUp bus imbalance.
pub struct R3RoundTraces<'a> {
    pub a: &'a mut RowMajorMatrix<F>,
    pub b: &'a mut RowMajorMatrix<F>,
    pub l: &'a mut RowMajorMatrix<F>,
    pub j: &'a mut RowMajorMatrix<F>,
    pub o: &'a mut RowMajorMatrix<F>,
    pub r: &'a mut RowMajorMatrix<F>,
    pub p: &'a mut RowMajorMatrix<F>,
}

/// Prove all seven R3 tables for a round and verify the proof (single process).
///
/// **EXPERIMENTAL** like the legacy harness: it uses the seed-based proving
/// config; the verifier-owned `prepare_*`/`prove_round`/`verify_round` split is
/// the remaining M7 work. What it *does* establish is that the R3 arithmetization
/// balances across all seven buses.
pub fn prove_and_verify_r3_round<H: ProvingHashSuite>(
    plan: &R3Plan,
    seed: u64,
    cfg: &ProverConfig,
) -> Result<(), String>
where
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    BatchProof<H::Config>: Sized,
{
    prove_and_verify_r3_round_with::<H>(plan, seed, cfg, |_| {})
}

/// Like [`prove_and_verify_r3_round`] but applies `tamper` to the freshly-built
/// main traces before committing. With an identity hook this is the honest path;
/// the M8 sweep passes mutations and asserts rejection.
pub fn prove_and_verify_r3_round_with<H: ProvingHashSuite>(
    plan: &R3Plan,
    seed: u64,
    cfg: &ProverConfig,
    tamper: impl FnOnce(&mut R3RoundTraces<'_>),
) -> Result<(), String>
where
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    BatchProof<H::Config>: Sized,
{
    // Verifier-owned shape validation (M7): reject a malformed public shape
    // (count identities, per-bus no-wrap, max height) before any expensive work.
    // The verifier reconstructs this shape from the public inputs and runs the
    // identical check.
    round_shape(plan)
        .validate()
        .map_err(|e| format!("invalid round shape: {e:?}"))?;

    // -- traces from the plan --
    let (mut a, a_real, a_height) = table_ar::build_trace(&plan.a_rows);

    // Table B: feed-forward then terminal occurrences; modes from scalar counts.
    let mut b_inputs: Vec<State> = Vec::with_capacity(plan.arena.n_perm());
    b_inputs.extend(plan.arena.feed_forward().iter().map(|io| io.input));
    b_inputs.extend(plan.arena.terminal().iter().map(|io| io.input));
    let mut b_modes: Vec<bool> = vec![true; plan.arena.n_ff()];
    b_modes.extend(std::iter::repeat_n(false, plan.arena.n_term()));
    let (mut b, b_real, b_height) = table_b::build_trace(&b_inputs);

    let (mut l, l_real, l_height) = table_l::build_trace(&plan.leaves);
    let (mut j, j_real, j_height) = table_j::build_trace(&plan.joins);
    let (mut o, o_real, o_height) = table_o::build_trace(&plan.opens);
    let mut r = table_r::build_main(&plan.r_mults);
    let mut p = table_p::build_main(&plan.p_mults);

    // M8 tamper hook (identity for the honest path).
    {
        let mut handle = R3RoundTraces {
            a: &mut a,
            b: &mut b,
            l: &mut l,
            j: &mut j,
            o: &mut o,
            r: &mut r,
            p: &mut p,
        };
        tamper(&mut handle);
    }

    let make_airs = || {
        vec![
            R3Air::A(TableArAir::new(a_height, a_real)),
            R3Air::B(TableBAir::new(b_height, b_real, b_modes.clone())),
            R3Air::L(TableLAir::new(l_height, l_real)),
            R3Air::J(TableJAir::new(j_height, j_real)),
            R3Air::O(TableOAir::new(o_height, o_real)),
            R3Air::R(TableRAir::default()),
            R3Air::P(TablePAir::default()),
        ]
    };
    let traces = [&a, &b, &l, &j, &o, &r, &p];

    let zero = [F::default(); 8];
    let old_root = plan.old_root.unwrap_or(zero);
    let publics_a = table_ar::public_values(&old_root, &plan.new_root, plan.old_root_is_none);
    let pv: Vec<Vec<F>> = vec![publics_a, vec![], vec![], vec![], vec![], vec![], vec![]];

    let config = H::build_config(seed, cfg);
    let airs = make_airs();
    let instances0: Vec<StarkInstance<'_, H::Config, R3Air>> = airs
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

    let airs_v = make_airs();
    verify_batch(&config, &airs_v, &proof, &pv, &prover_data.common).map_err(|e| format!("{e:?}"))
}

#[cfg(test)]
mod tamper;
#[cfg(test)]
mod tests;
