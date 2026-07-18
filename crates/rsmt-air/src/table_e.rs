//! Table E — byte range (DEVPLAN M3).
//!
//! 256 preprocessed rows `byte = 0..=255` (height is already a power of two, so
//! no padding) and one free witness column `mult`, the per-byte send count for
//! Bus 5 (wired in M4). `mult` is locally unconstrained — its correctness comes
//! from the LogUp balance, not a local rule — so Table E has no local
//! constraints.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use crate::cols::width_of;

pub const TABLE_E_HEIGHT: usize = 256;

/// Preprocessed columns (1).
#[repr(C)]
pub struct EPrepCols<T> {
    pub byte: T,
}

/// Main columns (1).
#[repr(C)]
pub struct EMainCols<T> {
    pub mult: T,
}

pub const TABLE_E_PREP_WIDTH: usize = width_of::<EPrepCols<u8>>();
pub const TABLE_E_WIDTH: usize = width_of::<EMainCols<u8>>();

#[derive(Clone, Default)]
pub struct TableEAir;

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableEAir {
    fn width(&self) -> usize {
        TABLE_E_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let data = (0..TABLE_E_HEIGHT).map(|i| F::from_u32(i as u32)).collect();
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
        // No local constraints: `mult` is free, tied to receivers by Bus 5.
    }
}

/// Build Table E's main trace from per-byte multiplicities.
pub fn build_main(e_mults: &[u32; 256]) -> RowMajorMatrix<BabyBear> {
    let data = e_mults.iter().map(|&m| BabyBear::from_u32(m)).collect();
    RowMajorMatrix::new(data, TABLE_E_WIDTH)
}

#[cfg(test)]
mod tests {
    use p3_matrix::Matrix;

    use super::*;

    #[test]
    fn preprocessed_is_0_to_255() {
        let air = TableEAir;
        let m = <TableEAir as BaseAir<BabyBear>>::preprocessed_trace(&air).unwrap();
        assert_eq!(m.height(), 256);
        for i in 0..256 {
            assert_eq!(m.values[i], BabyBear::from_u32(i as u32));
        }
    }
}
