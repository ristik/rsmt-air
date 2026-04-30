//! Table E (u8 range) — 256 rows, 1 preprocessed column `byte` (0..=255) plus
//! 1 main witness column `mult` (per-byte send multiplicity on Bus 5).
//!
//! Bus 5 (`u8`) wiring: Table E sends `(byte)` at multiplicity `mult`, where
//! `mult` is the count of N rows (across Table A) at that depth. Receivers:
//! Table A on `is_real * is_n` rows, sending the `depth` column. The witness
//! builder computes the per-byte counts; LogUp balance enforces correctness.

use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{Air, AirBuilder, AirLayout, BaseAir, SymbolicExpression, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Direction, Kind, Lookup, LookupAir, LookupInput};
use p3_matrix::dense::RowMajorMatrix;

pub const TABLE_E_HEIGHT: usize = 256;
pub const TABLE_E_WIDTH: usize = 1;
pub const TABLE_E_PREP_WIDTH: usize = 1;

pub const BUS_U8_NAME: &str = "u8";

#[derive(Clone)]
pub struct TableEAir {
    pub num_lookups: usize,
}

impl TableEAir {
    pub const fn new() -> Self {
        Self { num_lookups: 0 }
    }
}

impl Default for TableEAir {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableEAir {
    fn width(&self) -> usize {
        TABLE_E_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(TABLE_E_HEIGHT);
        for i in 0..TABLE_E_HEIGHT {
            data.push(F::from_u32(i as u32));
        }
        Some(RowMajorMatrix::new(data, TABLE_E_PREP_WIDTH))
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

impl<AB: AirBuilder> Air<AB> for TableEAir
where
    AB::F: Send,
{
    fn eval(&self, _builder: &mut AB) {
        // No local constraints — `mult` is unconstrained witness; LogUp
        // multiset balance is the only thing tying it to A's `depth` queries.
    }
}

impl<F: Field> LookupAir<F> for TableEAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.num_lookups = 0;
        let layout = AirLayout {
            main_width: TABLE_E_WIDTH,
            preprocessed_width: TABLE_E_PREP_WIDTH,
            ..Default::default()
        };
        let sb = SymbolicAirBuilder::<F>::new(layout);
        let main = sb.main();
        let main_local = main.current_slice();
        let prep = sb.preprocessed();
        let prep_local = prep.current_slice();

        let tuple: Vec<SymbolicExpression<F>> = vec![prep_local[0].into()];
        let mult: SymbolicExpression<F> = main_local[0].into();
        let inputs: Vec<LookupInput<F>> = vec![(tuple, mult, Direction::Send)];
        let lk = LookupAir::register_lookup(self, Kind::Global(BUS_U8_NAME.to_string()), &inputs);
        vec![lk]
    }
}

/// Build Table E's preprocessed trace (column `byte` = 0..=255).
pub fn build_preprocessed_babybear() -> RowMajorMatrix<BabyBear> {
    let air = TableEAir::new();
    <TableEAir as BaseAir<BabyBear>>::preprocessed_trace(&air).expect("preprocessed")
}

/// Build Table E's main trace (`mult` per byte) by counting how many N rows
/// in Table A request each depth value. The caller passes the un-padded
/// real rows (depth values from N rows only).
pub fn build_main_babybear(depths: impl IntoIterator<Item = u8>) -> RowMajorMatrix<BabyBear> {
    let mut counts = [0u32; TABLE_E_HEIGHT];
    for d in depths {
        counts[d as usize] += 1;
    }
    let mut data = Vec::with_capacity(TABLE_E_HEIGHT);
    for c in counts {
        data.push(BabyBear::from_u32(c));
    }
    RowMajorMatrix::new(data, TABLE_E_WIDTH)
}

#[cfg(test)]
mod tests {
    use p3_matrix::Matrix;

    use super::*;

    #[test]
    fn table_e_preprocessed_is_0_to_255() {
        let m = build_preprocessed_babybear();
        assert_eq!(m.height(), 256);
        assert_eq!(m.width, 1);
        for i in 0..256 {
            assert_eq!(m.values[i], BabyBear::from_u32(i as u32));
        }
    }

    #[test]
    fn table_e_mults_count_depths() {
        let depths = vec![0u8, 1, 1, 2, 2, 2, 255];
        let m = build_main_babybear(depths);
        assert_eq!(m.values[0], BabyBear::from_u32(1));
        assert_eq!(m.values[1], BabyBear::from_u32(2));
        assert_eq!(m.values[2], BabyBear::from_u32(3));
        assert_eq!(m.values[255], BabyBear::from_u32(1));
    }
}
