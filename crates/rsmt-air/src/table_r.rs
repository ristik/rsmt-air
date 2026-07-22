//! Table R — variable-width range table `R10` (DEVPLAN R2, D12).
//!
//! Preprocessed rows enumerate every `(bits, value)` with `0 ≤ bits ≤ 10` and
//! `0 ≤ value < 2^bits` — `Σ_{b=0}^{10} 2^b = 2047` real rows, padded to 2048.
//! A single free witness column `mult` is the per-`(bits,value)` receive count
//! for the range bus (wired in M4). Any `x < 2^k` is proved by decomposing `x`
//! into radix-1024 digits and looking each up as `(width, digit)` — no
//! complement, no wide multiply. R10 subsumes the byte range (`(8, value)`), so
//! it replaces Table E.
//!
//! Local constraint: padding hygiene — a padding row's `mult` is zero.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_witness::r10::{R10_REAL, r10_rows};

use crate::cols::{cast, width_of};

/// Number of real rows: `Σ_{b=0}^{10} 2^b = 2^11 − 1`.
pub const TABLE_R_REAL: usize = R10_REAL;
/// Padded height (next power of two).
pub const TABLE_R_HEIGHT: usize = R10_REAL + 1;

pub const BUS_RANGE_NAME: &str = "range";

/// Preprocessed columns: the bit width, the value, and the real/padding flag.
#[repr(C)]
pub struct RPrepCols<T> {
    pub bits: T,
    pub value: T,
    pub is_real: T,
}

/// Main columns: the per-entry multiplicity (free; tied by the range bus in M4).
#[repr(C)]
pub struct RMainCols<T> {
    pub mult: T,
}

pub const TABLE_R_PREP_WIDTH: usize = width_of::<RPrepCols<u8>>();
pub const TABLE_R_WIDTH: usize = width_of::<RMainCols<u8>>();

#[derive(Clone, Default)]
pub struct TableRAir {
    pub num_lookups: usize,
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableRAir {
    fn width(&self) -> usize {
        TABLE_R_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(TABLE_R_HEIGHT * TABLE_R_PREP_WIDTH);
        for (bits, value) in r10_rows() {
            data.push(F::from_u32(bits));
            data.push(F::from_u32(value));
            data.push(F::ONE);
        }
        // one padding row to reach the power of two
        for _ in TABLE_R_REAL..TABLE_R_HEIGHT {
            data.push(F::ZERO);
            data.push(F::ZERO);
            data.push(F::ZERO);
        }
        Some(RowMajorMatrix::new(data, TABLE_R_PREP_WIDTH))
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

impl<AB: AirBuilder> Air<AB> for TableRAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let prep = builder.preprocessed();
        let m: &RMainCols<AB::Var> = cast(main.current_slice());
        let p: &RPrepCols<AB::Var> = cast(prep.current_slice());
        // Padding hygiene: mult = 0 on padding rows.
        builder.assert_zero((AB::Expr::ONE - p.is_real.into()) * m.mult.into());
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableRAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        use p3_air::AirLayout;
        use p3_air::symbolic::SymbolicAirBuilder;
        use p3_lookup::{Direction, Kind, LookupInput};
        self.num_lookups = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: TABLE_R_WIDTH,
            preprocessed_width: TABLE_R_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        // Send (bits, value) at multiplicity `mult` (zero on the padding row).
        let inputs: Vec<LookupInput<F>> = vec![(
            vec![pl[0].into(), pl[1].into()],
            ml[0].into(),
            Direction::Send,
        )];
        vec![p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_RANGE_NAME.to_string()),
            &inputs,
        )]
    }
}

/// Build Table R's main trace from per-entry multiplicities (indexed by row
/// order of [`r10_rows`]).
pub fn build_main(mults: &[u32]) -> RowMajorMatrix<BabyBear> {
    assert!(mults.len() <= TABLE_R_REAL);
    let mut data = vec![BabyBear::ZERO; TABLE_R_HEIGHT * TABLE_R_WIDTH];
    for (i, &m) in mults.iter().enumerate() {
        data[i] = BabyBear::from_u32(m);
    }
    RowMajorMatrix::new(data, TABLE_R_WIDTH)
}

#[cfg(test)]
mod tests {
    use p3_air::check_constraints;
    use p3_matrix::Matrix;
    use rsmt_witness::r10::r10_index;

    use super::*;

    #[test]
    fn enumeration_is_complete_and_indexed() {
        let air = TableRAir::default();
        let m = <TableRAir as BaseAir<BabyBear>>::preprocessed_trace(&air).unwrap();
        assert_eq!(m.height(), TABLE_R_HEIGHT);
        let rows: Vec<(u32, u32)> = r10_rows().collect();
        assert_eq!(rows.len(), TABLE_R_REAL);
        for (i, (bits, value)) in rows.iter().enumerate() {
            assert_eq!(r10_index(*bits, *value), i);
            assert_eq!(m.values[i * TABLE_R_PREP_WIDTH], BabyBear::from_u32(*bits));
            assert_eq!(
                m.values[i * TABLE_R_PREP_WIDTH + 1],
                BabyBear::from_u32(*value)
            );
        }
    }

    #[test]
    fn padding_hygiene() {
        let air = TableRAir::default();
        let trace = build_main(&[]);
        check_constraints(&air, &trace, &[]);

        let mut bad = trace.clone();
        bad.values[TABLE_R_REAL] = BabyBear::from_u32(3); // padding row mult
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &bad, &[]);
        }));
        assert!(r.is_err(), "padding-row mult must be zero");
    }
}
