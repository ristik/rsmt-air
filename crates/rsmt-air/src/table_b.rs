//! Table B — vectorized Poseidon2 (DEVPLAN M3).
//!
//! The main trace is exactly Plonky3's `VectorizedPoseidon2Air` layout: the
//! deduplicated permutation arena (M2) chunked `P2_VECTOR_LEN` lanes per row.
//! The inner AIR's constraints accept exactly genuine Poseidon2 evaluations
//! per lane; a preprocessed lane mask marks real vs padding lanes (Bus 2 sends
//! are gated by it in M4). Table B is the single source of truth that every
//! in-circuit "hash" is a real Poseidon2.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::{
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
    BABYBEAR_S_BOX_DEGREE, BabyBear, GenericPoseidon2LinearLayersBabyBear,
};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::{
    RoundConstants, VectorizedPoseidon2Air, generate_vectorized_trace_rows, num_cols,
};

use rsmt_hash::{DIGEST_WIDTH, STATE_WIDTH, State, babybear_round_constants_16};
use rsmt_witness::TracePlan;

pub const P2_WIDTH: usize = STATE_WIDTH;
pub const P2_LOG_VECTOR_LEN: u8 = 3;
pub const P2_VECTOR_LEN: usize = 1 << P2_LOG_VECTOR_LEN;
pub const P2_SBOX_DEGREE: u64 = BABYBEAR_S_BOX_DEGREE;
pub const P2_SBOX_REGISTERS: usize = 1;
pub const P2_PARTIAL_ROUNDS: usize = BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16;
pub const P2_HALF_FULL_ROUNDS: usize = BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS;

pub const BUS_POSEIDON2_TUPLE_WIDTH: usize = 2 * STATE_WIDTH;

const FULL_ROUND_WIDTH: usize = P2_WIDTH * (P2_SBOX_REGISTERS + 1);
const PARTIAL_ROUND_WIDTH: usize = P2_SBOX_REGISTERS + 1;
pub const P2_PERM_WIDTH: usize = num_cols::<
    P2_WIDTH,
    P2_SBOX_DEGREE,
    P2_SBOX_REGISTERS,
    P2_HALF_FULL_ROUNDS,
    P2_PARTIAL_ROUNDS,
>();
/// Column offset of a lane's output state within its permutation block.
pub const P2_OUTPUT_OFFSET: usize = P2_WIDTH
    + P2_HALF_FULL_ROUNDS * FULL_ROUND_WIDTH
    + P2_PARTIAL_ROUNDS * PARTIAL_ROUND_WIDTH
    + (P2_HALF_FULL_ROUNDS - 1) * FULL_ROUND_WIDTH
    + P2_WIDTH * P2_SBOX_REGISTERS;

type TableBRoundConstants =
    RoundConstants<BabyBear, P2_WIDTH, P2_HALF_FULL_ROUNDS, P2_PARTIAL_ROUNDS>;

type TableBInnerAir = VectorizedPoseidon2Air<
    BabyBear,
    GenericPoseidon2LinearLayersBabyBear,
    P2_WIDTH,
    P2_SBOX_DEGREE,
    P2_SBOX_REGISTERS,
    P2_HALF_FULL_ROUNDS,
    P2_PARTIAL_ROUNDS,
    P2_VECTOR_LEN,
>;

/// Feed-forward Bus 2 (D17): full `(input[16], output[16])` for perms whose
/// entire output is another sponge block's input (node prefixes, non-final leaf
/// steps). Terminal Bus 2: `(input[16], output[0..8])` — digest only — for perms
/// whose tail is discarded (children blocks, final leaf step). Splitting the bus
/// (rather than a masked tail) keeps every tuple **and** multiplicity degree 1.
pub const BUS_P2FF_NAME: &str = "p2ff";
pub const BUS_P2TERM_NAME: &str = "p2term";

/// Preprocessed columns per row: for each lane a `(ff_mask, term_mask)` pair —
/// the send multiplicity for the feed-forward / terminal bus respectively. Each
/// is `real && mode` / `real && !mode`, a single degree-1 column (no product in
/// the LogUp, and no extra column in the fixed `VectorizedPoseidon2Air` trace).
pub const P2_PREP_WIDTH: usize = 2 * P2_VECTOR_LEN;

pub struct TableBAir {
    pub padded_height: usize,
    pub real_perms: usize,
    /// Per-perm feed-forward (`true`) / terminal (`false`) tags, length
    /// `real_perms`; from `plan.arena.modes()`.
    modes: Vec<bool>,
    constants: TableBRoundConstants,
    inner: TableBInnerAir,
    pub num_lookups: usize,
}

impl Clone for TableBAir {
    fn clone(&self) -> Self {
        let constants = self.constants.clone();
        Self {
            padded_height: self.padded_height,
            real_perms: self.real_perms,
            modes: self.modes.clone(),
            inner: VectorizedPoseidon2Air::new(constants.clone()),
            constants,
            num_lookups: self.num_lookups,
        }
    }
}

impl TableBAir {
    pub fn new(padded_height: usize, real_perms: usize, modes: Vec<bool>) -> Self {
        debug_assert_eq!(modes.len(), real_perms, "one mode per real perm");
        let constants = babybear_round_constants_16();
        let inner = VectorizedPoseidon2Air::new(constants.clone());
        Self {
            padded_height,
            real_perms,
            modes,
            constants,
            inner,
            num_lookups: 0,
        }
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableBAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        use p3_air::symbolic::{SymbolicAirBuilder, SymbolicExpression};
        use p3_air::{AirLayout, WindowAccess};
        use p3_lookup::{Direction, Kind};
        type SE<F> = SymbolicExpression<F>;
        self.num_lookups = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: P2_PERM_WIDTH * P2_VECTOR_LEN,
            preprocessed_width: P2_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        // Bus 2 split (D17): each lane sends the full (input[16], output[16]) to
        // the feed-forward bus at `ff_mask`, and the digest (input[16],
        // output[0..8]) to the terminal bus at `term_mask`. Exactly one mask is
        // set per real perm, so the perm lands on its single bus.
        let mut lookups = Vec::with_capacity(2 * P2_VECTOR_LEN);
        for lane in 0..P2_VECTOR_LEN {
            let base = lane * P2_PERM_WIDTH;
            let ff_mask: SE<F> = pl[2 * lane].into();
            let term_mask: SE<F> = pl[2 * lane + 1].into();
            let mut input: Vec<SE<F>> = Vec::with_capacity(16);
            for j in 0..16 {
                input.push(ml[base + j].into());
            }
            let out = |j: usize| -> SE<F> { ml[base + P2_OUTPUT_OFFSET + j].into() };

            let mut ff: Vec<SE<F>> = input.clone();
            for j in 0..16 {
                ff.push(out(j));
            }
            lookups.push(p3_lookup::LookupAir::register_lookup(
                self,
                Kind::Global(BUS_P2FF_NAME.to_string()),
                &[(ff, ff_mask, Direction::Send)],
            ));

            let mut term: Vec<SE<F>> = input;
            for j in 0..8 {
                term.push(out(j));
            }
            lookups.push(p3_lookup::LookupAir::register_lookup(
                self,
                Kind::Global(BUS_P2TERM_NAME.to_string()),
                &[(term, term_mask, Direction::Send)],
            ));
        }
        lookups
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableBAir {
    fn width(&self) -> usize {
        P2_PERM_WIDTH * P2_VECTOR_LEN
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(self.padded_height * P2_PREP_WIDTH);
        for row in 0..self.padded_height {
            for lane in 0..P2_VECTOR_LEN {
                let perm_idx = row * P2_VECTOR_LEN + lane;
                let real = perm_idx < self.real_perms;
                let mode = real && self.modes[perm_idx];
                data.push(F::from_bool(mode)); // ff_mask
                data.push(F::from_bool(real && !mode)); // term_mask
            }
        }
        Some(RowMajorMatrix::new(data, P2_PREP_WIDTH))
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB> Air<AB> for TableBAir
where
    AB: AirBuilder<F = BabyBear>,
{
    fn eval(&self, builder: &mut AB) {
        self.inner.eval(builder);
    }
}

pub fn padded_height_for_perms(real_perms: usize) -> usize {
    real_perms
        .div_ceil(P2_VECTOR_LEN)
        .max(1)
        .next_power_of_two()
        .max(2)
}

/// Build Table B's trace from a list of permutation inputs (the M2 arena).
/// Returns `(trace, real_perms, height)`.
pub fn build_trace(inputs: &[State]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = inputs.len();
    let height = padded_height_for_perms(real);
    let padded_perms = height * P2_VECTOR_LEN;
    let mut padded_inputs = Vec::with_capacity(padded_perms);
    padded_inputs.extend_from_slice(inputs);
    padded_inputs.resize(padded_perms, [BabyBear::ZERO; STATE_WIDTH]);

    let constants = babybear_round_constants_16();
    let trace = generate_vectorized_trace_rows::<
        BabyBear,
        GenericPoseidon2LinearLayersBabyBear,
        P2_WIDTH,
        P2_SBOX_DEGREE,
        P2_SBOX_REGISTERS,
        P2_HALF_FULL_ROUNDS,
        P2_PARTIAL_ROUNDS,
        P2_VECTOR_LEN,
    >(padded_inputs, &constants, 0);

    debug_assert_eq!(trace.height(), height);
    debug_assert_eq!(trace.width, P2_PERM_WIDTH * P2_VECTOR_LEN);
    (trace, real, height)
}

/// The permutation inputs Table B must evaluate: exactly the M2 arena, in
/// order (arena index = permutation index).
pub fn collect_inputs(plan: &TracePlan) -> Vec<State> {
    plan.arena.entries().iter().map(|io| io.input).collect()
}

/// The per-perm Bus-2 tags (D17), aligned with [`collect_inputs`].
pub fn collect_modes(plan: &TracePlan) -> Vec<bool> {
    plan.arena.modes().to_vec()
}

const _: () = assert!(P2_OUTPUT_OFFSET + STATE_WIDTH == P2_PERM_WIDTH);
const _: () = assert!(DIGEST_WIDTH * 2 == STATE_WIDTH);

#[cfg(test)]
mod tests;
