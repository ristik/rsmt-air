//! Table P — powers of two (DEVPLAN M3, new table).
//!
//! 31 preprocessed rows `(r, 2^r)` for `r ∈ [0, 30]` (all powers fit BabyBear,
//! `2^30 < p`), plus an `is_real` flag, padded to 32. One free witness column
//! `mult` records the per-shift send count for Bus 7 (wired in M4).
//!
//! Local constraint: padding hygiene — a padding row's `mult` is zero, so it
//! contributes no spurious bus send.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use crate::cols::{cast, width_of};

/// Number of real power-of-two rows: `r ∈ [0, 30]`.
pub const TABLE_P_REAL: usize = 31;
/// Padded height (next power of two).
pub const TABLE_P_HEIGHT: usize = 32;

/// Preprocessed columns: the exponent, the power, and the real/padding flag.
#[repr(C)]
pub struct PPrepCols<T> {
    pub r: T,
    pub pow: T,
    pub is_real: T,
}

/// Main columns: the per-shift multiplicity (free; tied by Bus 7 in M4).
#[repr(C)]
pub struct PMainCols<T> {
    pub mult: T,
}

pub const TABLE_P_PREP_WIDTH: usize = width_of::<PPrepCols<u8>>();
pub const TABLE_P_WIDTH: usize = width_of::<PMainCols<u8>>();

pub const BUS_POW2_NAME: &str = "pow2";

#[derive(Clone, Default)]
pub struct TablePAir {
    /// Aux-column counter used while registering lookups.
    pub num_lookups: usize,
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TablePAir {
    fn width(&self) -> usize {
        TABLE_P_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(TABLE_P_HEIGHT * TABLE_P_PREP_WIDTH);
        for r in 0..TABLE_P_HEIGHT {
            if r < TABLE_P_REAL {
                data.push(F::from_u32(r as u32));
                data.push(F::from_u32(1u32 << r));
                data.push(F::ONE);
            } else {
                data.push(F::ZERO);
                data.push(F::ZERO);
                data.push(F::ZERO);
            }
        }
        Some(RowMajorMatrix::new(data, TABLE_P_PREP_WIDTH))
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

impl<AB: AirBuilder> Air<AB> for TablePAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let main_row = main.current_slice();
        let prep = builder.preprocessed();
        let prep_row = prep.current_slice();
        let m: &PMainCols<AB::Var> = cast(main_row);
        let p: &PPrepCols<AB::Var> = cast(prep_row);

        // Padding hygiene: mult = 0 on padding rows.
        builder.assert_zero((AB::Expr::ONE - p.is_real.into()) * m.mult.into());
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TablePAir {
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
            main_width: TABLE_P_WIDTH,
            preprocessed_width: TABLE_P_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        // Send (r, 2^r) at multiplicity `mult` (zero on the padding row).
        let tuple = vec![pl[0].into(), pl[1].into()];
        let mult = ml[0].into();
        let inputs: Vec<LookupInput<F>> = vec![(tuple, mult, Direction::Send)];
        vec![p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_POW2_NAME.to_string()),
            &inputs,
        )]
    }
}

/// Build Table P's main trace from the per-exponent multiplicities.
pub fn build_main(p_mults: &[u32; 31]) -> RowMajorMatrix<BabyBear> {
    let mut data = Vec::with_capacity(TABLE_P_HEIGHT * TABLE_P_WIDTH);
    for r in 0..TABLE_P_HEIGHT {
        let m = p_mults.get(r).copied().unwrap_or(0);
        data.push(BabyBear::from_u32(m));
    }
    RowMajorMatrix::new(data, TABLE_P_WIDTH)
}

#[cfg(test)]
mod tests {
    use p3_air::check_constraints;
    use p3_matrix::Matrix;

    use super::*;

    #[test]
    fn prep_is_powers_of_two() {
        let air = TablePAir::default();
        let m = <TablePAir as BaseAir<BabyBear>>::preprocessed_trace(&air).unwrap();
        assert_eq!(m.height(), TABLE_P_HEIGHT);
        for r in 0..TABLE_P_REAL {
            assert_eq!(
                m.values[r * TABLE_P_PREP_WIDTH],
                BabyBear::from_u32(r as u32)
            );
            assert_eq!(
                m.values[r * TABLE_P_PREP_WIDTH + 1],
                BabyBear::from_u32(1u32 << r)
            );
        }
    }

    #[test]
    fn constraints_pass_and_padding_hygiene() {
        let air = TablePAir::default();
        let mut mults = [0u32; 31];
        mults[5] = 3;
        mults[30] = 1;
        let trace = build_main(&mults);
        check_constraints(&air, &trace, &[]);

        // A nonzero mult on the padding row must violate.
        let mut bad = trace.clone();
        bad.values[TABLE_P_REAL] = BabyBear::from_u32(9); // padding row mult
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &bad, &[]);
        }));
        assert!(r.is_err(), "padding-row mult must be constrained to zero");
    }
}
