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
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::StarkGenericConfig;

use rsmt_air::table_ar::TableArAir;
use rsmt_air::table_j::TableJAir;
use rsmt_air::table_l::TableLAir;
use rsmt_air::table_o::TableOAir;
use rsmt_air::{
    R3Air, TableBAir, TablePAir, TableRAir, table_ar, table_b, table_j, table_l, table_o, table_p,
    table_r,
};
use rsmt_hash::State;
use rsmt_witness::r3build::{R3Plan, R3Shape};

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
/// The verify step reconstructs its preprocessing (`CommonData`) from AIRs built
/// **from the shape alone** — it never consumes the prover's `ProverData` (S10,
/// M7). The remaining non-verifier-owned input is the seed-based proving config
/// (fixed by `r3_fixed_poseidon2_config` / removed in M10) and the cross-process
/// serialization boundary.
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

    // -- Verifier-owned preprocessing (M7, S10) --
    // The verifier reconstructs `CommonData` (the preprocessing commitment +
    // lookup definitions) from AIRs it builds *from the shape alone*, plus the
    // padded heights — it never touches the prover's traces or `ProverData`.
    // `CommonData` is a deterministic function of `(config, airs, heights)`, so
    // the reconstruction equals the prover's and the proof still verifies.
    let is_zk = config.is_zk();
    let heights = [
        a.height(),
        b.height(),
        l.height(),
        j.height(),
        o.height(),
        r.height(),
        p.height(),
    ];
    // Heights are powers of two, so log2 = trailing_zeros.
    let degree_bits: Vec<usize> = heights
        .iter()
        .map(|&h| h.trailing_zeros() as usize + is_zk)
        .collect();
    let mut airs_v = make_airs();
    let verifier_common =
        ProverData::from_airs_and_degrees(&config, &mut airs_v, &degree_bits).common;

    verify_batch(&config, &airs_v, &proof, &pv, &verifier_common).map_err(|e| format!("{e:?}"))
}

/// Authoritative padded heights `[A,B,L,J,O,R,P]` from the scalar shape — the
/// SAME derivation the prover's `build_trace` uses, so a verifier can size its
/// AIRs from the public shape alone (M7 cross-process boundary).
pub fn r3_padded_heights(shape: &R3Shape) -> [usize; 7] {
    let pad = |n: usize| n.next_power_of_two().max(2);
    let n_perm = shape.n_p2ff + shape.n_p2term;
    [
        pad(shape.n_ops),
        rsmt_air::table_b::padded_height_for_perms(n_perm),
        pad(shape.n_leaf),
        pad(shape.n_join),
        pad(shape.n_open),
        2048,
        32,
    ]
}

/// The seven R3 AIRs built **from the public shape alone** (no witness/plan).
fn r3_airs_from_shape(shape: &R3Shape) -> Vec<R3Air> {
    let h = r3_padded_heights(shape);
    let n_perm = shape.n_p2ff + shape.n_p2term;
    let mut b_modes = vec![true; shape.n_p2ff];
    b_modes.extend(std::iter::repeat_n(false, shape.n_p2term));
    vec![
        R3Air::A(TableArAir::new(h[0], shape.n_ops)),
        R3Air::B(TableBAir::new(h[1], n_perm, b_modes)),
        R3Air::L(TableLAir::new(h[2], shape.n_leaf)),
        R3Air::J(TableJAir::new(h[3], shape.n_join)),
        R3Air::O(TableOAir::new(h[4], shape.n_open)),
        R3Air::R(TableRAir::default()),
        R3Air::P(TablePAir::default()),
    ]
}

/// **Prover side.** Prove one R3 round, returning the batch proof. The companion
/// [`verify_r3_round`] needs only the proof, the public inputs, and the scalar
/// shape — no `ProverData`, no plan (M7 prove/verify split).
pub fn prove_r3_round<H: ProvingHashSuite>(
    plan: &R3Plan,
    seed: u64,
    cfg: &ProverConfig,
) -> BatchProof<H::Config>
where
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    BatchProof<H::Config>: Sized,
{
    let (a, a_real, a_height) = table_ar::build_trace(&plan.a_rows);
    let mut b_inputs: Vec<State> = Vec::with_capacity(plan.arena.n_perm());
    b_inputs.extend(plan.arena.feed_forward().iter().map(|io| io.input));
    b_inputs.extend(plan.arena.terminal().iter().map(|io| io.input));
    let mut b_modes: Vec<bool> = vec![true; plan.arena.n_ff()];
    b_modes.extend(std::iter::repeat_n(false, plan.arena.n_term()));
    let (b, b_real, b_height) = table_b::build_trace(&b_inputs);
    let (l, l_real, l_height) = table_l::build_trace(&plan.leaves);
    let (j, j_real, j_height) = table_j::build_trace(&plan.joins);
    let (o, o_real, o_height) = table_o::build_trace(&plan.opens);
    let r = table_r::build_main(&plan.r_mults);
    let p = table_p::build_main(&plan.p_mults);
    let traces = [&a, &b, &l, &j, &o, &r, &p];

    let airs = vec![
        R3Air::A(TableArAir::new(a_height, a_real)),
        R3Air::B(TableBAir::new(b_height, b_real, b_modes)),
        R3Air::L(TableLAir::new(l_height, l_real)),
        R3Air::J(TableJAir::new(j_height, j_real)),
        R3Air::O(TableOAir::new(o_height, o_real)),
        R3Air::R(TableRAir::default()),
        R3Air::P(TablePAir::default()),
    ];
    let zero = [F::default(); 8];
    let old_root = plan.old_root.unwrap_or(zero);
    let publics_a = table_ar::public_values(&old_root, &plan.new_root, plan.old_root_is_none);
    let pv: Vec<Vec<F>> = vec![publics_a, vec![], vec![], vec![], vec![], vec![], vec![]];

    let config = H::build_config(seed, cfg);
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
    prove_batch(&config, &instances, &prover_data)
}

/// **Verifier side.** Verify a round from *only* the proof, the public inputs
/// `[old_root[8], new_root[8], old_root_is_none]`, and the scalar `shape`. Rebuilds
/// the AIRs and reconstructs `CommonData` from the shape alone — nothing the
/// prover created crosses this boundary (S10). The shape is validated first.
pub fn verify_r3_round<H: ProvingHashSuite>(
    seed: u64,
    cfg: &ProverConfig,
    shape: &R3Shape,
    publics: &[F],
    proof: &BatchProof<H::Config>,
) -> Result<(), String>
where
    p3_batch_stark::Domain<H::Config>: PolynomialSpace<Val = F>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    BatchProof<H::Config>: Sized,
{
    rsmt_protocol::RoundShape {
        n_ops: shape.n_ops,
        n_leaf: shape.n_leaf,
        n_join: shape.n_join,
        n_open: shape.n_open,
        n_b11: shape.n_b11,
        n_p2ff: shape.n_p2ff,
        n_p2term: shape.n_p2term,
    }
    .validate()
    .map_err(|e| format!("invalid round shape: {e:?}"))?;

    let config = H::build_config(seed, cfg);
    let mut airs = r3_airs_from_shape(shape);
    let is_zk = config.is_zk();
    let degree_bits: Vec<usize> = r3_padded_heights(shape)
        .iter()
        .map(|&h| h.trailing_zeros() as usize + is_zk)
        .collect();
    let common = ProverData::from_airs_and_degrees(&config, &mut airs, &degree_bits).common;
    let pv: Vec<Vec<F>> = vec![
        publics.to_vec(),
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
    ];
    verify_batch(&config, &airs, proof, &pv, &common).map_err(|e| format!("{e:?}"))
}

/// Per-table sizing for one R3 round (cells = padded height × (main + prep)).
#[derive(Debug, Clone)]
pub struct R3TableCells {
    pub name: &'static str,
    pub real: usize,
    pub padded: usize,
    pub main: usize,
    pub prep: usize,
}

impl R3TableCells {
    pub fn cells(&self) -> usize {
        self.padded * (self.main + self.prep)
    }
}

/// The per-table cost breakdown of an R3 round (widths are layout constants;
/// heights derive from the plan). No proving — pure sizing for the cost model.
pub fn r3_round_cells(plan: &R3Plan) -> Vec<R3TableCells> {
    use rsmt_air::table_ar::{TABLE_AR_PREP_WIDTH, TABLE_AR_WIDTH};
    use rsmt_air::table_j::{TABLE_J_PREP_WIDTH, TABLE_J_WIDTH};
    use rsmt_air::table_l::{TABLE_L_PREP_WIDTH, TABLE_L_WIDTH};
    use rsmt_air::table_o::{TABLE_O_PREP_WIDTH, TABLE_O_WIDTH};

    let pad = |n: usize| n.next_power_of_two().max(2);
    let s = &plan.shape;
    let b_rows = (s.n_p2ff + s.n_p2term).div_ceil(8);
    vec![
        R3TableCells {
            name: "A",
            real: s.n_ops,
            padded: pad(s.n_ops),
            main: TABLE_AR_WIDTH,
            prep: TABLE_AR_PREP_WIDTH,
        },
        R3TableCells {
            name: "B",
            real: b_rows,
            padded: pad(b_rows),
            main: 2384,
            prep: 16,
        },
        R3TableCells {
            name: "L",
            real: s.n_leaf,
            padded: pad(s.n_leaf),
            main: TABLE_L_WIDTH,
            prep: TABLE_L_PREP_WIDTH,
        },
        R3TableCells {
            name: "J",
            real: s.n_join,
            padded: pad(s.n_join),
            main: TABLE_J_WIDTH,
            prep: TABLE_J_PREP_WIDTH,
        },
        R3TableCells {
            name: "O",
            real: s.n_open,
            padded: pad(s.n_open),
            main: TABLE_O_WIDTH,
            prep: TABLE_O_PREP_WIDTH,
        },
        R3TableCells {
            name: "R",
            real: 2047,
            padded: 2048,
            main: 1,
            prep: 3,
        },
        R3TableCells {
            name: "P",
            real: 31,
            padded: 32,
            main: 1,
            prep: 3,
        },
    ]
}

#[cfg(test)]
mod tamper;
#[cfg(test)]
mod tests;
