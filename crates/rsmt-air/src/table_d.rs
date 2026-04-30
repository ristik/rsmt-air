//! Table D (batch input) — preprocessed-only.
//!
//! Materializes the trusted, externally-sorted batch as a preprocessed trace
//! with columns `(idx, is_real_d, key[9], value[9])` (20 cols). Sends
//! `(idx, key[0..9], value[0..9])` on Bus 6 at multiplicity `is_real_d`.

use num_bigint::BigUint;
use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{Air, AirBuilder, AirLayout, BaseAir, SymbolicExpression, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Direction, Kind, Lookup, LookupAir, LookupInput};
use p3_matrix::dense::RowMajorMatrix;

use rsmt_hash::{LIMBS, pack_biguint, pack_value_32};

use crate::table_c::{BUS_BATCH_NAME, BUS_BATCH_TUPLE_WIDTH};

/// Dummy main column (always zero); Plonky3 batch-stark currently expects a
/// non-empty main trace per instance. The column is unconstrained.
pub const TABLE_D_WIDTH: usize = 1;
pub const TABLE_D_PREP_WIDTH: usize = 2 + LIMBS + LIMBS; // = 20

const D_P_IDX: usize = 0;
const D_P_IS_REAL: usize = 1;
const D_P_KEY: usize = 2;
const D_P_VAL: usize = 2 + LIMBS;

#[derive(Clone)]
pub struct TableDAir {
    pub padded_height: usize,
    /// Optionally embed the batch so `preprocessed_trace` produces real data;
    /// when `None`, falls back to zeros (placeholder, used only for tests
    /// that don't actually exercise the bus).
    pub batch: Option<Vec<(BigUint, Vec<u8>)>>,
    pub num_lookups: usize,
}

impl TableDAir {
    pub fn for_batch(batch: &[(BigUint, Vec<u8>)]) -> Self {
        let h = batch.len().next_power_of_two().max(2);
        Self {
            padded_height: h,
            batch: Some(batch.to_vec()),
            num_lookups: 0,
        }
    }

    /// Verifier-side constructor: shape only, no batch data. The batch lives in
    /// the global preprocessed commitment (in `CommonData`); the verifier needs
    /// only the AIR's shape (width, height, lookups) to fold constraints.
    pub fn shape_only(padded_height: usize) -> Self {
        Self {
            padded_height,
            batch: None,
            num_lookups: 0,
        }
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableDAir {
    fn width(&self) -> usize {
        TABLE_D_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h * TABLE_D_PREP_WIDTH);
        if let Some(batch) = &self.batch {
            for (i, (k, v)) in batch.iter().enumerate() {
                data.push(F::from_u32(i as u32));
                data.push(F::ONE);
                let kl = pack_biguint(k);
                let vl = pack_value_32(v);
                for limb in kl {
                    data.push(F::from_u32(limb_to_u32(limb)));
                }
                for limb in vl {
                    data.push(F::from_u32(limb_to_u32(limb)));
                }
            }
            for _ in batch.len()..h {
                for _ in 0..TABLE_D_PREP_WIDTH {
                    data.push(F::ZERO);
                }
            }
        } else {
            for _ in 0..h * TABLE_D_PREP_WIDTH {
                data.push(F::ZERO);
            }
        }
        Some(RowMajorMatrix::new(data, TABLE_D_PREP_WIDTH))
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

fn limb_to_u32(b: BabyBear) -> u32 {
    use p3_field::PrimeField32;
    b.as_canonical_u32()
}

impl<AB: AirBuilder> Air<AB> for TableDAir
where
    AB::F: Send,
{
    fn eval(&self, _builder: &mut AB) {
        // No local constraints — consumed by Bus 6 only.
    }
}

impl<F: Field> LookupAir<F> for TableDAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.num_lookups = 0;
        let layout = AirLayout {
            main_width: TABLE_D_WIDTH,
            preprocessed_width: TABLE_D_PREP_WIDTH,
            ..Default::default()
        };
        let sb = SymbolicAirBuilder::<F>::new(layout);
        let prep = sb.preprocessed();
        let prep_local = prep.current_slice();

        let is_real_d: SymbolicExpression<F> = prep_local[D_P_IS_REAL].into();
        let mut tuple: Vec<SymbolicExpression<F>> = Vec::with_capacity(BUS_BATCH_TUPLE_WIDTH);
        tuple.push(prep_local[D_P_IDX].into());
        for j in 0..LIMBS {
            tuple.push(prep_local[D_P_KEY + j].into());
        }
        for j in 0..LIMBS {
            tuple.push(prep_local[D_P_VAL + j].into());
        }
        let inputs: Vec<LookupInput<F>> = vec![(tuple, is_real_d, Direction::Send)];
        let lk =
            LookupAir::register_lookup(self, Kind::Global(BUS_BATCH_NAME.to_string()), &inputs);
        vec![lk]
    }
}

/// Build Table D's preprocessed trace from an already-sorted batch.
pub fn build_preprocessed_babybear(
    sorted_batch: &[(BigUint, Vec<u8>)],
) -> RowMajorMatrix<BabyBear> {
    TableDAir::for_batch(sorted_batch)
        .preprocessed_trace()
        .expect("preprocessed")
}

#[cfg(test)]
mod tests {
    use p3_matrix::Matrix;

    use super::*;

    #[test]
    fn table_d_preprocessed_packs_batch() {
        let batch: Vec<(BigUint, Vec<u8>)> = vec![
            (BigUint::from(0x12345678u64), vec![0xAA; 32]),
            (BigUint::from(0x9abcdef0u64), vec![0xBB; 32]),
        ];
        let m = build_preprocessed_babybear(&batch);
        assert_eq!(m.height(), 2);
        assert_eq!(m.width, TABLE_D_PREP_WIDTH);
        assert_eq!(m.values[0], BabyBear::ZERO);
        assert_eq!(m.values[1], BabyBear::from_u32(1));
        assert_eq!(m.values[TABLE_D_PREP_WIDTH], BabyBear::from_u32(1));
    }
}
