//! Table C (leaf sponge) AIR — three rows per `L`, with sponge transition
//! constraints that fix `state_in` from the previous row's `state_out` plus
//! the per-step injection of key/value limbs. `state_out` is tied to
//! `Poseidon2(state_in)` via Bus 2 (deferred to M7).
//!
//! Layout:
//!   Main (50 cols):  key[0..9] | value[9..18] | state_in[18..34] | state_out[34..50]
//!   Preprocessed (5 cols): leaf_idx | is_step_0 | is_step_1 | is_step_2 | is_real_c

use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{Air, AirBuilder, AirLayout, BaseAir, BaseLeaf, SymbolicExpression, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Direction, Kind, Lookup, LookupAir, LookupInput};
use p3_matrix::dense::RowMajorMatrix;

use rsmt_hash::{DIGEST_WIDTH, DOMAIN_LEAF, LIMBS, STATE_WIDTH};
use rsmt_witness::TableCRow;

use crate::table_b::{BUS_POSEIDON2_NAME, BUS_POSEIDON2_TUPLE_WIDTH};

pub const TABLE_C_WIDTH: usize = LIMBS + LIMBS + STATE_WIDTH + STATE_WIDTH; // 9+9+16+16 = 50
pub const TABLE_C_PREP_WIDTH: usize = 1 + 3 + 1; // leaf_idx + 3 step indicators + is_real_c

const C_KEY: usize = 0; // 9 cols
const C_VAL: usize = 9; // 9 cols
const C_STATE_IN: usize = 18; // 16 cols
const C_STATE_OUT: usize = 34; // 16 cols

const P_LEAF_IDX: usize = 0;
const P_IS_STEP_0: usize = 1;
const P_IS_STEP_1: usize = 2;
const P_IS_STEP_2: usize = 3;
const P_IS_REAL_C: usize = 4;

pub const BUS_LEAF_HASH_NAME: &str = "leaf_hash";
pub const BUS_LEAF_HASH_TUPLE_WIDTH: usize = 1 + DIGEST_WIDTH; // 9

pub const BUS_BATCH_NAME: &str = "batch";
pub const BUS_BATCH_TUPLE_WIDTH: usize = 1 + LIMBS + LIMBS; // 19

#[derive(Clone)]
pub struct TableCAir {
    pub padded_height: usize,
    pub real_rows: usize,
    pub num_lookups: usize,
}

impl TableCAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableCAir {
    fn width(&self) -> usize {
        TABLE_C_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h * TABLE_C_PREP_WIDTH);
        for i in 0..h {
            let is_real = i < self.real_rows;
            let leaf_idx = if is_real { (i / 3) as u32 } else { 0 };
            let step = if is_real { i % 3 } else { 0xFF };
            data.push(F::from_u32(leaf_idx));
            data.push(F::from_bool(is_real && step == 0));
            data.push(F::from_bool(is_real && step == 1));
            data.push(F::from_bool(is_real && step == 2));
            data.push(F::from_bool(is_real));
        }
        Some(RowMajorMatrix::new(data, TABLE_C_PREP_WIDTH))
    }

    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for TableCAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice().to_vec();
        let next = main.next_slice().to_vec();
        let prep = builder.preprocessed();
        let prep_local = prep.current_slice().to_vec();
        let prep_next = prep.next_slice().to_vec();

        let one = AB::Expr::ONE;
        let domain_leaf = AB::Expr::from(AB::F::from_u32(DOMAIN_LEAF));

        let is_real_c = prep_local[P_IS_REAL_C];
        let is_step_0 = prep_local[P_IS_STEP_0];
        let is_step_1_next = prep_next[P_IS_STEP_1];
        let is_step_2_next = prep_next[P_IS_STEP_2];

        // Padding: every witness column is zero on non-real rows.
        let not_real = one.clone() - is_real_c;
        for j in 0..TABLE_C_WIDTH {
            builder.assert_zero(not_real.clone() * local[j]);
        }

        // Step 0 initialization: state_in is fully determined by key.
        // state_in[0] = DOMAIN_LEAF
        builder.assert_zero(is_step_0 * (local[C_STATE_IN + 0] - domain_leaf.clone()));
        // state_in[1+j] = key[j] for j=0..7
        for j in 0..7 {
            builder.assert_zero(is_step_0 * (local[C_STATE_IN + 1 + j] - local[C_KEY + j]));
        }
        // state_in[8..16] = 0
        for j in 0..8 {
            builder.assert_zero(is_step_0 * local[C_STATE_IN + 8 + j]);
        }

        // Cross-row transitions: when next is step 1 or step 2, next.state_in
        // is constrained against local.state_out + injection.
        //
        // Step 1 injection (indices into state_in): [0]+=key[7], [1]+=key[8],
        // [2..8]+=value[0..6]. Indices [8..16] carry from prev.
        for j in 0..STATE_WIDTH {
            let inj_step1 = match j {
                0 => local[C_KEY + 7].into(),
                1 => local[C_KEY + 8].into(),
                2..=7 => local[C_VAL + (j - 2)].into(),
                _ => AB::Expr::ZERO,
            };
            let inj_step2: AB::Expr = match j {
                0 => local[C_VAL + 6].into(),
                1 => local[C_VAL + 7].into(),
                2 => local[C_VAL + 8].into(),
                _ => AB::Expr::ZERO,
            };
            builder.assert_zero(
                is_step_1_next * (next[C_STATE_IN + j] - local[C_STATE_OUT + j] - inj_step1),
            );
            builder.assert_zero(
                is_step_2_next * (next[C_STATE_IN + j] - local[C_STATE_OUT + j] - inj_step2),
            );
        }

        // Continuity of key/value across same-leaf transitions (when next is
        // step 1 or step 2, i.e., not a leaf boundary).
        let cont = is_step_1_next + is_step_2_next;
        for j in 0..LIMBS {
            builder.assert_zero(cont.clone() * (next[C_KEY + j] - local[C_KEY + j]));
            builder.assert_zero(cont.clone() * (next[C_VAL + j] - local[C_VAL + j]));
        }
    }
}

impl<F: Field> LookupAir<F> for TableCAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.num_lookups = 0;
        let layout = AirLayout {
            main_width: TABLE_C_WIDTH,
            preprocessed_width: TABLE_C_PREP_WIDTH,
            ..Default::default()
        };
        let sb = SymbolicAirBuilder::<F>::new(layout);
        let main = sb.main();
        let main_local = main.current_slice();
        let prep = sb.preprocessed();
        let prep_local = prep.current_slice();

        let is_last_step: SymbolicExpression<F> = prep_local[P_IS_STEP_2].into();

        // Bus 4 (leaf_hash) send: (leaf_idx, state_out[0..8]) on last step.
        let mut leaf_tuple: Vec<SymbolicExpression<F>> =
            Vec::with_capacity(BUS_LEAF_HASH_TUPLE_WIDTH);
        leaf_tuple.push(prep_local[P_LEAF_IDX].into());
        for j in 0..DIGEST_WIDTH {
            leaf_tuple.push(main_local[C_STATE_OUT + j].into());
        }
        let leaf_inputs: Vec<LookupInput<F>> =
            vec![(leaf_tuple, is_last_step.clone(), Direction::Send)];
        let leaf_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_LEAF_HASH_NAME.to_string()),
            &leaf_inputs,
        );

        // Bus 6 (batch) receive: (leaf_idx, key[9], value[9]) on last step.
        let mut batch_tuple: Vec<SymbolicExpression<F>> = Vec::with_capacity(BUS_BATCH_TUPLE_WIDTH);
        batch_tuple.push(prep_local[P_LEAF_IDX].into());
        for j in 0..LIMBS {
            batch_tuple.push(main_local[C_KEY + j].into());
        }
        for j in 0..LIMBS {
            batch_tuple.push(main_local[C_VAL + j].into());
        }
        let batch_inputs: Vec<LookupInput<F>> =
            vec![(batch_tuple, is_last_step, Direction::Receive)];
        let batch_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_BATCH_NAME.to_string()),
            &batch_inputs,
        );

        // Bus 2 (Poseidon2) receive: each real C row is one sponge
        // permutation, with the full input and full output state.
        let is_real_c: SymbolicExpression<F> = prep_local[P_IS_REAL_C].into();
        let mut p2_tuple: Vec<SymbolicExpression<F>> =
            Vec::with_capacity(BUS_POSEIDON2_TUPLE_WIDTH);
        for j in 0..STATE_WIDTH {
            p2_tuple.push(main_local[C_STATE_IN + j].into());
        }
        for j in 0..STATE_WIDTH {
            p2_tuple.push(main_local[C_STATE_OUT + j].into());
        }
        let p2_inputs: Vec<LookupInput<F>> = vec![(p2_tuple, is_real_c, Direction::Receive)];
        let p2_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_POSEIDON2_NAME.to_string()),
            &p2_inputs,
        );

        let _ = SymbolicExpression::<F>::Leaf(BaseLeaf::Constant(F::ONE));
        vec![leaf_lookup, batch_lookup, p2_lookup]
    }
}

/// Build Table C's main trace (BabyBear) from witness rows; pads to the next
/// power-of-two height (≥ 2). Returns `(trace, real, height)`.
pub fn build_trace_babybear(rows: &[TableCRow]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = rows.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_C_WIDTH);
    for r in rows {
        for j in 0..LIMBS {
            data.push(r.key[j]);
        }
        for j in 0..LIMBS {
            data.push(r.value[j]);
        }
        for j in 0..STATE_WIDTH {
            data.push(r.state_in[j]);
        }
        for j in 0..STATE_WIDTH {
            data.push(r.state_out[j]);
        }
    }
    for _ in real..height {
        for _ in 0..TABLE_C_WIDTH {
            data.push(BabyBear::ZERO);
        }
    }
    (RowMajorMatrix::new(data, TABLE_C_WIDTH), real, height)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use p3_air::check_constraints;
    use rand::{RngExt, SeedableRng};
    use rand_xoshiro::Xoshiro256PlusPlus;

    use rsmt_witness::build_table_c;

    use super::*;

    #[test]
    fn table_c_constraints_pass() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(13);
        let batch: Vec<(BigUint, Vec<u8>)> = (0..8)
            .map(|_| {
                let mut k = [0u8; 32];
                rng.fill(&mut k);
                let mut v = [0u8; 32];
                rng.fill(&mut v);
                (BigUint::from_bytes_be(&k), v.to_vec())
            })
            .collect();
        let rows = build_table_c(&batch);
        let (trace, real, height) = build_trace_babybear(&rows);
        let air = TableCAir::new(height, real);
        check_constraints(&air, &trace, &[]);
    }
}
