//! M9 gate: a minimal, standalone full-FRI regression for **two linear lookup
//! entries paired into one global LogUp context** (`DEVPLAN-R3.md` §5.9). The
//! plan requires this to pass *before* any round AIR pairs its receives, because
//! the historical `OodEvaluationMismatch` came from grouping.
//!
//! Setup: a `Sender` table sends `(value)` on a global bus with a multiplicity;
//! a `Pair` table receives **two** values per row, both `Direction::Receive`,
//! **grouped in a single `register_lookup`** (one aux running-sum column). If the
//! pinned Plonky3 supports global two-entry contexts, the batch balances and
//! verifies.

#![cfg(test)]

use p3_air::symbolic::{SymbolicAirBuilder, SymbolicExpression};
use p3_air::{Air, AirBuilder, AirLayout, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_batch_stark::{ProverData, StarkInstance, prove_batch, verify_batch};
use p3_field::PrimeCharacteristicRing;
use p3_lookup::{Direction, Kind, Lookup, LookupAir};
use p3_matrix::dense::RowMajorMatrix;

use crate::config::ProverConfig;
use crate::proof_hash::{F, Poseidon2ProofHash, ProvingHashSuite};

const BUS: &str = "pairtest";
type SE = SymbolicExpression<F>;

// -- Sender: main [value, mult]; sends (value) with multiplicity `mult`. -------
#[derive(Clone)]
struct Sender {
    height: usize,
    real: usize,
    n: usize,
}

impl<G: PrimeCharacteristicRing + Send + Sync> BaseAir<G> for Sender {
    fn width(&self) -> usize {
        2
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<G>> {
        let mut d = Vec::with_capacity(self.height);
        for i in 0..self.height {
            d.push(G::from_bool(i < self.real));
        }
        Some(RowMajorMatrix::new(d, 1))
    }
    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for Sender
where
    AB::F: Send,
{
    fn eval(&self, _builder: &mut AB) {}
}

impl LookupAir<F> for Sender {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let i = self.n;
        self.n += 1;
        vec![i]
    }
    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.n = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: 2,
            preprocessed_width: 1,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let value: SE = ml[0].into();
        let mult: SE = ml[1].into();
        vec![LookupAir::register_lookup(
            self,
            Kind::Global(BUS.to_string()),
            &[(vec![value], mult, Direction::Send)],
        )]
    }
}

// -- Pair: main [a, b]; receives a and b, GROUPED in one register_lookup. ------
#[derive(Clone)]
struct Pair {
    height: usize,
    real: usize,
    n: usize,
    /// `true`: group both receives in one context (the candidate optimization);
    /// `false`: two separate one-entry contexts (the current, working design).
    paired: bool,
}

impl<G: PrimeCharacteristicRing + Send + Sync> BaseAir<G> for Pair {
    fn width(&self) -> usize {
        2
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<G>> {
        let mut d = Vec::with_capacity(self.height);
        for i in 0..self.height {
            d.push(G::from_bool(i < self.real));
        }
        Some(RowMajorMatrix::new(d, 1))
    }
    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for Pair
where
    AB::F: Send,
{
    fn eval(&self, _builder: &mut AB) {}
}

impl LookupAir<F> for Pair {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let i = self.n;
        self.n += 1;
        vec![i]
    }
    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.n = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: 2,
            preprocessed_width: 1,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        let a: SE = ml[0].into();
        let b: SE = ml[1].into();
        let is_real: SE = pl[0].into();
        if self.paired {
            // TWO receives grouped into ONE context (the candidate optimization).
            vec![LookupAir::register_lookup(
                self,
                Kind::Global(BUS.to_string()),
                &[
                    (vec![a], is_real.clone(), Direction::Receive),
                    (vec![b], is_real, Direction::Receive),
                ],
            )]
        } else {
            // Two separate one-entry contexts (the current, working design).
            vec![
                LookupAir::register_lookup(
                    self,
                    Kind::Global(BUS.to_string()),
                    &[(vec![a], is_real.clone(), Direction::Receive)],
                ),
                LookupAir::register_lookup(
                    self,
                    Kind::Global(BUS.to_string()),
                    &[(vec![b], is_real, Direction::Receive)],
                ),
            ]
        }
    }
}

#[derive(Clone)]
enum PairTestAir {
    S(Sender),
    P(Pair),
}
macro_rules! d {
    ($s:ident, $a:ident => $e:expr) => {
        match $s {
            Self::S($a) => $e,
            Self::P($a) => $e,
        }
    };
}
impl<G: PrimeCharacteristicRing + Send + Sync> BaseAir<G> for PairTestAir {
    fn width(&self) -> usize {
        d!(self, a => BaseAir::<G>::width(a))
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<G>> {
        d!(self, a => BaseAir::<G>::preprocessed_trace(a))
    }
    fn num_public_values(&self) -> usize {
        d!(self, a => BaseAir::<G>::num_public_values(a))
    }
}
impl<AB: AirBuilder<F = BabyBear>> Air<AB> for PairTestAir {
    fn eval(&self, b: &mut AB) {
        d!(self, a => Air::<AB>::eval(a, b))
    }
}
impl LookupAir<F> for PairTestAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        d!(self, a => LookupAir::<F>::add_lookup_columns(a))
    }
    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        d!(self, a => LookupAir::<F>::get_lookups(a))
    }
}

fn pad(n: usize) -> usize {
    n.next_power_of_two().max(2)
}

/// Run the sender/receiver batch with the receiver in `paired` or unpaired mode.
/// Returns `true` iff it proves and verifies (a `prove_batch` panic on the
/// internal `check_constraints` counts as failure).
fn run(paired: bool) -> bool {
    let rows: [(u32, u32); 6] = [(1, 2), (2, 3), (3, 1), (1, 3), (2, 2), (3, 3)];
    let mut counts = std::collections::BTreeMap::<u32, u32>::new();
    for &(a, b) in &rows {
        *counts.entry(a).or_default() += 1;
        *counts.entry(b).or_default() += 1;
    }
    let senders: Vec<(u32, u32)> = counts.into_iter().collect();

    let p_real = rows.len();
    let p_h = pad(p_real);
    let mut p_main = Vec::with_capacity(p_h * 2);
    for &(a, b) in &rows {
        p_main.push(F::from_u32(a));
        p_main.push(F::from_u32(b));
    }
    p_main.resize(p_h * 2, F::ZERO);
    let p_trace = RowMajorMatrix::new(p_main, 2);

    let s_real = senders.len();
    let s_h = pad(s_real);
    let mut s_main = Vec::with_capacity(s_h * 2);
    for &(v, m) in &senders {
        s_main.push(F::from_u32(v));
        s_main.push(F::from_u32(m));
    }
    s_main.resize(s_h * 2, F::ZERO);
    let s_trace = RowMajorMatrix::new(s_main, 2);

    let make = || {
        vec![
            PairTestAir::S(Sender {
                height: s_h,
                real: s_real,
                n: 0,
            }),
            PairTestAir::P(Pair {
                height: p_h,
                real: p_real,
                n: 0,
                paired,
            }),
        ]
    };
    let traces = [&s_trace, &p_trace];
    let pv: Vec<Vec<F>> = vec![vec![], vec![]];

    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let config = Poseidon2ProofHash::build_config(7, &ProverConfig::default());
        let airs = make();
        let instances0: Vec<StarkInstance<'_, _, PairTestAir>> = airs
            .iter()
            .zip(traces.iter())
            .map(|(air, trace)| StarkInstance {
                air,
                trace,
                public_values: vec![],
                lookups: vec![],
            })
            .collect();
        let prover_data = ProverData::from_instances(&config, &instances0);
        let traces_refs: Vec<&RowMajorMatrix<F>> = traces.to_vec();
        let instances = StarkInstance::new_multiple(&airs, &traces_refs, &pv, &prover_data.common);
        let proof = prove_batch(&config, &instances, &prover_data);
        let airs_v = make();
        verify_batch(&config, &airs_v, &proof, &pv, &prover_data.common)
    }));
    std::panic::set_hook(prev);
    matches!(r, Ok(Ok(())))
}

/// M9 gate result: with the pinned Plonky3 rev, an **unpaired** global bus (one
/// entry per context) balances, but **grouping two same-direction receives into
/// one global context** fails with `OodEvaluationMismatch`. Per the risk
/// register ("Two-entry LogUp causes degree/OOD failures → keep one entry per
/// context"), R3 therefore does **not** pair global-bus receives. This test is a
/// regression guard: if a Plonky3 upgrade makes pairing work, the second
/// assertion flips and M9 pairing can be revisited.
#[test]
fn global_two_entry_pairing_is_unsupported_in_pinned_plonky3() {
    assert!(run(false), "unpaired (one entry per context) must verify");
    assert!(
        !run(true),
        "paired two-entry global context unexpectedly verified — revisit M9 pairing"
    );
}
