//! Table B: vectorized Poseidon2 permutation AIR plus Bus 2 sends.
//!
//! The main trace is exactly Plonky3's `VectorizedPoseidon2Air` layout. Real
//! versus padded permutation lanes live in preprocessed lane-mask columns, so
//! the inner AIR can borrow its row with the exact width it expects.

use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{Air, AirBuilder, AirLayout, BaseAir, SymbolicExpression, WindowAccess};
use p3_baby_bear::{
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
    BABYBEAR_S_BOX_DEGREE, BabyBear, GenericPoseidon2LinearLayersBabyBear,
};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Direction, Kind, Lookup, LookupAir, LookupInput};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::{
    RoundConstants, VectorizedPoseidon2Air, generate_vectorized_trace_rows, num_cols,
};

use rsmt_hash::{DIGEST_WIDTH, STATE_WIDTH, State, babybear_round_constants_16, node_hash_input};
use rsmt_witness::{TableCRow, TableFRow};

pub const P2_WIDTH: usize = STATE_WIDTH;
pub const P2_LOG_VECTOR_LEN: u8 = 3;
pub const P2_VECTOR_LEN: usize = 1 << P2_LOG_VECTOR_LEN;
pub const P2_SBOX_DEGREE: u64 = BABYBEAR_S_BOX_DEGREE;
pub const P2_SBOX_REGISTERS: usize = 1;
pub const P2_PARTIAL_ROUNDS: usize = BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16;
pub const P2_HALF_FULL_ROUNDS: usize = BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS;

pub const BUS_POSEIDON2_NAME: &str = "p2";
pub const BUS_POSEIDON2_TUPLE_WIDTH: usize = 2 * STATE_WIDTH;

const FULL_ROUND_WIDTH: usize = P2_WIDTH * (P2_SBOX_REGISTERS + 1);
const PARTIAL_ROUND_WIDTH: usize = P2_SBOX_REGISTERS + 1;
const P2_PERM_WIDTH: usize = num_cols::<
    P2_WIDTH,
    P2_SBOX_DEGREE,
    P2_SBOX_REGISTERS,
    P2_HALF_FULL_ROUNDS,
    P2_PARTIAL_ROUNDS,
>();
const P2_OUTPUT_OFFSET: usize = P2_WIDTH
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

pub struct TableBAir {
    pub padded_height: usize,
    pub real_perms: usize,
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
            inner: VectorizedPoseidon2Air::new(constants.clone()),
            constants,
            num_lookups: self.num_lookups,
        }
    }
}

impl TableBAir {
    pub fn new(padded_height: usize, real_perms: usize) -> Self {
        let constants = babybear_round_constants_16();
        let inner = VectorizedPoseidon2Air::new(constants.clone());
        Self {
            padded_height,
            real_perms,
            constants,
            inner,
            num_lookups: 0,
        }
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableBAir {
    fn width(&self) -> usize {
        P2_PERM_WIDTH * P2_VECTOR_LEN
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(self.padded_height * P2_VECTOR_LEN);
        for row in 0..self.padded_height {
            for lane in 0..P2_VECTOR_LEN {
                let perm_idx = row * P2_VECTOR_LEN + lane;
                data.push(F::from_bool(perm_idx < self.real_perms));
            }
        }
        Some(RowMajorMatrix::new(data, P2_VECTOR_LEN))
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

impl<F: Field> LookupAir<F> for TableBAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.num_lookups = 0;
        let layout = AirLayout {
            main_width: P2_PERM_WIDTH * P2_VECTOR_LEN,
            preprocessed_width: P2_VECTOR_LEN,
            ..Default::default()
        };
        let sb = SymbolicAirBuilder::<F>::new(layout);
        let main = sb.main();
        let main_local = main.current_slice();
        let prep = sb.preprocessed();
        let prep_local = prep.current_slice();

        let mut lookups = Vec::with_capacity(P2_VECTOR_LEN);
        for lane in 0..P2_VECTOR_LEN {
            let base = lane * P2_PERM_WIDTH;
            let mut tuple = Vec::with_capacity(BUS_POSEIDON2_TUPLE_WIDTH);
            for j in 0..STATE_WIDTH {
                tuple.push(main_local[base + j].into());
            }
            for j in 0..STATE_WIDTH {
                tuple.push(main_local[base + P2_OUTPUT_OFFSET + j].into());
            }
            let mult: SymbolicExpression<F> = prep_local[lane].into();
            let inputs: Vec<LookupInput<F>> = vec![(tuple, mult, Direction::Send)];
            lookups.push(LookupAir::register_lookup(
                self,
                Kind::Global(BUS_POSEIDON2_NAME.to_string()),
                &inputs,
            ));
        }
        lookups
    }
}

pub fn padded_height_for_perms(real_perms: usize) -> usize {
    real_perms
        .div_ceil(P2_VECTOR_LEN)
        .max(1)
        .next_power_of_two()
        .max(2)
}

pub fn build_trace_babybear(inputs: &[State]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
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

pub fn collect_poseidon2_inputs(c_rows: &[TableCRow], f_rows: &[TableFRow]) -> Vec<State> {
    let old_hashes = f_rows.iter().filter(|r| r.b11).count();
    let mut inputs = Vec::with_capacity(c_rows.len() + f_rows.len() + old_hashes);

    for row in c_rows {
        inputs.push(row.state_in);
    }
    for row in f_rows {
        inputs.push(node_hash_input(&row.left_new, &row.right_new, row.depth));
        if row.b11 {
            inputs.push(node_hash_input(&row.left_old, &row.right_old, row.depth));
        }
    }

    inputs
}

const _: () = assert!(P2_OUTPUT_OFFSET + STATE_WIDTH == P2_PERM_WIDTH);
const _: () = assert!(DIGEST_WIDTH * 2 == STATE_WIDTH);
