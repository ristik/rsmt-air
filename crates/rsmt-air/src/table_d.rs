//! Table D — sorted batch (DEVPLAN M3, preprocessed-only).
//!
//! The trusted, externally-sorted batch lives entirely in preprocessed columns
//! `(idx, is_real, key[9], value[9])`; it is *sent* on Bus 6 (M4). The single
//! main column is a placeholder (batch-stark wants a non-empty main trace) and
//! is constrained to zero.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_core::LIMBS;
use rsmt_witness::DRow;

use crate::cols::{cast, width_of};

/// Radix-1024 digits per 9-limb key/value: limbs 0..7 → 3 digits each,
/// limb 8 → 2 digits, so `8·3 + 2 = 26` digits.
pub const N_INPUT_DIGITS: usize = 26;

/// Preprocessed columns (72): the batch plus its canonical radix-1024 digits.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct DPrepCols<T> {
    pub idx: T,
    pub is_real: T,
    pub key: [T; LIMBS],
    pub value: [T; LIMBS],
    pub key_d: [T; N_INPUT_DIGITS],
    pub value_d: [T; N_INPUT_DIGITS],
}

/// Main columns (1): a constrained-zero placeholder.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct DMainCols<T> {
    pub dummy: T,
}

pub const TABLE_D_PREP_WIDTH: usize = width_of::<DPrepCols<u8>>();
pub const TABLE_D_WIDTH: usize = width_of::<DMainCols<u8>>();

/// One packed batch row: `(idx, key_limbs, value_limbs)`.
pub type BatchRow = (u32, [BabyBear; LIMBS], [BabyBear; LIMBS]);

pub const BUS_BATCH_NAME: &str = "batch";

#[derive(Clone)]
pub struct TableDAir {
    pub padded_height: usize,
    /// Packed batch rows; `None` on the verifier side (shape only — the batch
    /// lives in the preprocessed commitment).
    pub batch: Option<Vec<BatchRow>>,
    pub num_lookups: usize,
}

impl TableDAir {
    pub fn for_rows(rows: &[DRow]) -> Self {
        let batch = rows
            .iter()
            .map(|r| (r.idx, r.key, r.value))
            .collect::<Vec<_>>();
        Self {
            padded_height: rows.len().next_power_of_two().max(2),
            batch: Some(batch),
            num_lookups: 0,
        }
    }

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
        let n = self.batch.as_ref().map_or(0, |b| b.len());
        for i in 0..h {
            if let Some(batch) = &self.batch
                && i < n
            {
                let (idx, key, value) = &batch[i];
                data.push(F::from_u32(*idx));
                data.push(F::ONE);
                for l in key {
                    data.push(F::from_u32(limb(*l)));
                }
                for l in value {
                    data.push(F::from_u32(limb(*l)));
                }
                push_digits(&mut data, key);
                push_digits(&mut data, value);
                continue;
            }
            for _ in 0..TABLE_D_PREP_WIDTH {
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

fn limb(b: BabyBear) -> u32 {
    use p3_field::PrimeField32;
    b.as_canonical_u32()
}

/// Radix-1024 digits of the 9 limbs, in `DPrepCols::key_d/value_d` order:
/// limbs 0..7 → 3 digits each, limb 8 → 2 digits.
fn push_digits<F: PrimeCharacteristicRing>(data: &mut Vec<F>, limbs: &[BabyBear; LIMBS]) {
    for (j, l) in limbs.iter().enumerate() {
        let n = if j < 8 { 3 } else { 2 };
        let mut v = limb(*l);
        for _ in 0..n {
            data.push(F::from_u32(v & 0x3FF));
            v >>= 10;
        }
    }
}

/// Bit width of digit `d` (`0 ≤ d < 26`): 10 everywhere except limb 8's top
/// digit (index 25), which is 6.
pub const fn input_digit_width(d: usize) -> u32 {
    if d == N_INPUT_DIGITS - 1 { 6 } else { 10 }
}

impl<AB: AirBuilder> Air<AB> for TableDAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let (m, p): (DMainCols<AB::Var>, DPrepCols<AB::Var>) = {
            let main = builder.main();
            let prep = builder.preprocessed();
            (*cast(main.current_slice()), *cast(prep.current_slice()))
        };
        builder.assert_zero(m.dummy.into());

        // Canonical reconstruction: each limb = Σ digit·1024^i (gated by is_real,
        // so padding rows are exempt). Digit ranges are the range bus (below).
        let e = |v: AB::Var| -> AB::Expr { v.into() };
        let is_real = e(p.is_real);
        let d1024 = AB::Expr::from_u32(1 << 10);
        let d2048 = AB::Expr::from_u32(1 << 20);
        for j in 0..LIMBS {
            let (base, n) = if j < 8 { (3 * j, 3) } else { (24, 2) };
            let recon = |digits: &[AB::Var; N_INPUT_DIGITS]| -> AB::Expr {
                let mut acc = e(digits[base]);
                if n >= 2 {
                    acc += e(digits[base + 1]) * d1024.clone();
                }
                if n >= 3 {
                    acc += e(digits[base + 2]) * d2048.clone();
                }
                acc
            };
            builder.assert_zero(is_real.clone() * (e(p.key[j]) - recon(&p.key_d)));
            builder.assert_zero(is_real.clone() * (e(p.value[j]) - recon(&p.value_d)));
        }
    }
}

// DPrepCols preprocessed offsets.
const P_KEY_D: usize = 2 + 2 * LIMBS;
const P_VALUE_D: usize = 2 + 2 * LIMBS + N_INPUT_DIGITS;

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableDAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        use p3_air::AirLayout;
        use p3_air::symbolic::{SymbolicAirBuilder, SymbolicExpression};
        use p3_lookup::{Direction, Kind};
        type SE<F> = SymbolicExpression<F>;
        self.num_lookups = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: TABLE_D_WIDTH,
            preprocessed_width: TABLE_D_PREP_WIDTH,
            ..Default::default()
        });
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        // Bus 6 (batch): send (idx, key[9], value[9]) at multiplicity is_real.
        // DPrepCols: idx(0), is_real(1), key[2..11], value[11..20].
        let mut tuple: Vec<SE<F>> = vec![pl[0].into()];
        for j in 0..LIMBS {
            tuple.push(pl[2 + j].into());
        }
        for j in 0..LIMBS {
            tuple.push(pl[2 + LIMBS + j].into());
        }
        let is_real: SE<F> = pl[1].into();
        let mut lookups = vec![p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_BATCH_NAME.to_string()),
            &[(tuple, is_real.clone(), Direction::Send)],
        )];

        // Range bus: prove every key/value digit within its canonical width
        // (D15, #5). Fixed widths ⇒ degree-1 tuple.
        let konst = |v: u32| -> SE<F> {
            use p3_air::symbolic::BaseLeaf;
            SE::<F>::Leaf(BaseLeaf::Constant(F::from_u32(v)))
        };
        for d in 0..N_INPUT_DIGITS {
            let w = konst(input_digit_width(d));
            lookups.push(p3_lookup::LookupAir::register_lookup(
                self,
                Kind::Global(crate::table_r::BUS_RANGE_NAME.to_string()),
                &[(
                    vec![w.clone(), pl[P_KEY_D + d].into()],
                    is_real.clone(),
                    Direction::Receive,
                )],
            ));
            lookups.push(p3_lookup::LookupAir::register_lookup(
                self,
                Kind::Global(crate::table_r::BUS_RANGE_NAME.to_string()),
                &[(
                    vec![w, pl[P_VALUE_D + d].into()],
                    is_real.clone(),
                    Direction::Receive,
                )],
            ));
        }
        lookups
    }
}

/// Build Table D's main trace (all-zero placeholder column).
pub fn build_main(padded_height: usize) -> RowMajorMatrix<BabyBear> {
    RowMajorMatrix::new(
        vec![BabyBear::ZERO; padded_height * TABLE_D_WIDTH],
        TABLE_D_WIDTH,
    )
}

#[cfg(test)]
mod tests {
    use p3_air::check_constraints;

    use super::*;

    fn sample() -> Vec<DRow> {
        vec![
            DRow {
                idx: 0,
                key: [BabyBear::from_u32(3); LIMBS],
                value: [BabyBear::from_u32(7); LIMBS],
            },
            DRow {
                idx: 1,
                key: [BabyBear::from_u32(4); LIMBS],
                value: [BabyBear::from_u32(8); LIMBS],
            },
        ]
    }

    #[test]
    fn preprocessed_packs_and_pads() {
        let air = TableDAir::for_rows(&sample());
        let m = <TableDAir as BaseAir<BabyBear>>::preprocessed_trace(&air).unwrap();
        assert_eq!(m.width, TABLE_D_PREP_WIDTH);
        assert_eq!(m.values[1], BabyBear::ONE); // row 0 is_real
        assert_eq!(m.values[TABLE_D_PREP_WIDTH], BabyBear::ONE); // row1 idx
    }

    #[test]
    fn dummy_main_must_be_zero() {
        let air = TableDAir::for_rows(&sample());
        let trace = build_main(air.padded_height);
        check_constraints(&air, &trace, &[]);

        let mut bad = trace.clone();
        bad.values[0] = BabyBear::ONE;
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_constraints(&air, &bad, &[]);
        }));
        assert!(r.is_err(), "dummy column must be constrained to zero");
    }
}
