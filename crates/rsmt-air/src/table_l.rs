//! Table L — fused canonical leaf (R3/M4, `DEVPLAN-R3.md` §5.3). One row per
//! `L`/`O_l`, replacing Table C (three sponge rows) and Table D (batch +
//! canonical digits).
//!
//! ```text
//! a_row_idx, key_digits[26], value_digits[26], mid_0[16], mid_1[16], digest[8]
//! ```
//!
//! The nine key/value limbs are **linear expressions** in the 26 radix-1024
//! digits, never stored columns. The table is almost entirely bus-driven:
//!
//! - 52 `range` receives prove every digit canonical (`(width, digit)`);
//! - two `p2ff` receives bind leaf steps 0/1 (`input[16] → mid`);
//! - one `p2term` receive binds step 2 (`input[16] → digest[8]`);
//! - one `leaf` send exports `(a_row_idx, digest[8], key_limbs[9])` to Table A.
//!
//! Injectivity of the digit reconstruction (each digit `< 2^width`) is exactly
//! the byte-faithfulness property S4: an accepted row extracts to one 32-byte
//! key and one 32-byte value. The only *local* constraint is padding hygiene;
//! every semantic check rides a bus, so full validation is the M7 balance test.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_hash::DOMAIN_LEAF;
use rsmt_witness::r3plan::{N_LEAF_DIGITS, R3Leaf};

use crate::cols::{cast, width_of};

/// Main columns (93): a_row_idx, key_digits[26], value_digits[26], mid_0[16],
/// mid_1[16], digest[8].
#[repr(C)]
#[derive(Clone, Copy)]
pub struct LCols<T> {
    pub a_row_idx: T,
    pub key_digits: [T; N_LEAF_DIGITS],
    pub value_digits: [T; N_LEAF_DIGITS],
    pub mid_0: [T; 16],
    pub mid_1: [T; 16],
    pub digest: [T; 8],
}

/// Preprocessed columns (1): realness.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct LPrepCols<T> {
    pub is_real: T,
}

pub const TABLE_L_WIDTH: usize = width_of::<LCols<u8>>();
pub const TABLE_L_PREP_WIDTH: usize = width_of::<LPrepCols<u8>>();

const _: () = assert!(TABLE_L_WIDTH == 93);

// Column offsets into a main row (must match `LCols` field order).
const O_A_ROW_IDX: usize = 0;
const O_KEY_D: usize = 1;
const O_VAL_D: usize = O_KEY_D + N_LEAF_DIGITS; // 27
const O_MID0: usize = O_VAL_D + N_LEAF_DIGITS; // 53
const O_MID1: usize = O_MID0 + 16; // 69
const O_DIGEST: usize = O_MID1 + 16; // 85

/// Radix-1024 digit widths for the 26 leaf digits: `[10,10,10]×8 ++ [10,6]`.
const DIGIT_WIDTH: [u32; N_LEAF_DIGITS] = {
    let mut w = [10u32; N_LEAF_DIGITS];
    w[N_LEAF_DIGITS - 1] = 6; // limb 8's top digit is 6 bits
    w
};

/// Number of radix-1024 digits per limb `j` (`3` for the 30-bit limbs, `2` for
/// the 16-bit tail limb).
const fn limb_digits(j: usize) -> usize {
    if j < 8 { 3 } else { 2 }
}

/// First digit index of limb `j` in the 26-digit array.
const fn limb_digit_offset(j: usize) -> usize {
    if j < 8 { 3 * j } else { 24 }
}

pub const BUS_LEAF_NAME: &str = "leaf";

#[derive(Clone)]
pub struct TableLAir {
    pub padded_height: usize,
    pub real_rows: usize,
    pub num_lookups: usize,
}

impl TableLAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableLAir {
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
            main_width: TABLE_L_WIDTH,
            preprocessed_width: TABLE_L_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        let is_real: SE<F> = pl[0].into();

        // Linear reconstruction `limb_j = Σ digitᵢ · 1024ⁱ` from a digit base.
        let limb = |base: usize, j: usize| -> SE<F> {
            let off = base + limb_digit_offset(j);
            let mut acc = SE::<F>::ZERO;
            let mut weight = F::ONE;
            for i in 0..limb_digits(j) {
                acc += SE::<F>::from(ml[off + i]) * SE::<F>::from(weight);
                weight *= F::from_u32(1024);
            }
            acc
        };
        let key = |j: usize| limb(O_KEY_D, j);
        let val = |j: usize| limb(O_VAL_D, j);
        let mid0 = |i: usize| SE::<F>::from(ml[O_MID0 + i]);
        let mid1 = |i: usize| SE::<F>::from(ml[O_MID1 + i]);

        let mut lookups = Vec::new();

        // (a) 52 range receives: (width, digit) at multiplicity is_real.
        for k in 0..N_LEAF_DIGITS {
            for base in [O_KEY_D, O_VAL_D] {
                let tuple = vec![
                    SE::<F>::from(F::from_u32(DIGIT_WIDTH[k])),
                    SE::<F>::from(ml[base + k]),
                ];
                lookups.push(p3_lookup::LookupAir::register_lookup(
                    self,
                    Kind::Global(crate::table_r::BUS_RANGE_NAME.to_string()),
                    &[(tuple, is_real.clone(), Direction::Receive)],
                ));
            }
        }

        // (b) p2ff step 0: input = [DOMAIN_LEAF, key0..6, 0×8], output = mid_0.
        let mut ff0: Vec<SE<F>> = Vec::with_capacity(32);
        ff0.push(SE::<F>::from(F::from_u32(DOMAIN_LEAF)));
        for j in 0..7 {
            ff0.push(key(j));
        }
        for _ in 8..16 {
            ff0.push(SE::<F>::ZERO);
        }
        for i in 0..16 {
            ff0.push(mid0(i));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_b::BUS_P2FF_NAME.to_string()),
            &[(ff0, is_real.clone(), Direction::Receive)],
        ));

        // (c) p2ff step 1: input = mid_0 + [key7, key8, val0..5, 0×8], out = mid_1.
        let mut ff1: Vec<SE<F>> = Vec::with_capacity(32);
        for i in 0..16 {
            let inj = match i {
                0 => key(7),
                1 => key(8),
                2..=7 => val(i - 2),
                _ => SE::<F>::ZERO,
            };
            ff1.push(mid0(i) + inj);
        }
        for i in 0..16 {
            ff1.push(mid1(i));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_b::BUS_P2FF_NAME.to_string()),
            &[(ff1, is_real.clone(), Direction::Receive)],
        ));

        // (d) p2term step 2: input = mid_1 + [val6, val7, val8, 0×13], out = digest.
        let mut term: Vec<SE<F>> = Vec::with_capacity(24);
        for i in 0..16 {
            let inj = match i {
                0 => val(6),
                1 => val(7),
                2 => val(8),
                _ => SE::<F>::ZERO,
            };
            term.push(mid1(i) + inj);
        }
        for i in 0..8 {
            term.push(SE::<F>::from(ml[O_DIGEST + i]));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_b::BUS_P2TERM_NAME.to_string()),
            &[(term, is_real.clone(), Direction::Receive)],
        ));

        // (e) leaf send: (a_row_idx, digest[8], key_limbs[9]) to Table A.
        let mut leaf: Vec<SE<F>> = Vec::with_capacity(18);
        leaf.push(SE::<F>::from(ml[O_A_ROW_IDX]));
        for i in 0..8 {
            leaf.push(SE::<F>::from(ml[O_DIGEST + i]));
        }
        for j in 0..9 {
            leaf.push(key(j));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_LEAF_NAME.to_string()),
            &[(leaf, is_real.clone(), Direction::Send)],
        ));

        lookups
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableLAir {
    fn width(&self) -> usize {
        TABLE_L_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(self.padded_height * TABLE_L_PREP_WIDTH);
        for i in 0..self.padded_height {
            data.push(F::from_bool(i < self.real_rows));
        }
        Some(RowMajorMatrix::new(data, TABLE_L_PREP_WIDTH))
    }

    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for TableLAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let (row, is_real): (Vec<AB::Var>, AB::Var) = {
            let main = builder.main();
            let prep = builder.preprocessed();
            let pl: &LPrepCols<AB::Var> = cast(prep.current_slice());
            (main.current_slice().to_vec(), pl.is_real)
        };
        // Padding hygiene: every main column is zero on non-real rows. All
        // semantic constraints ride buses, so this is the only local rule.
        let not_real = AB::Expr::ONE - is_real.into();
        for cell in row {
            builder.assert_zero(not_real.clone() * cell.into());
        }
    }
}

// -- trace generation -------------------------------------------------------

/// Build Table L's main trace from the R3 leaf plan (one row per leaf).
pub fn build_trace(leaves: &[R3Leaf]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = leaves.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_L_WIDTH);
    for leaf in leaves {
        data.push(BabyBear::from_u32(leaf.a_row_idx));
        for &d in &leaf.key_digits {
            data.push(BabyBear::from_u32(d));
        }
        for &d in &leaf.value_digits {
            data.push(BabyBear::from_u32(d));
        }
        data.extend_from_slice(&leaf.mid_0);
        data.extend_from_slice(&leaf.mid_1);
        data.extend_from_slice(&leaf.digest);
    }
    for _ in real..height {
        data.extend(std::iter::repeat_n(BabyBear::ZERO, TABLE_L_WIDTH));
    }
    (RowMajorMatrix::new(data, TABLE_L_WIDTH), real, height)
}

#[cfg(test)]
mod tests;
