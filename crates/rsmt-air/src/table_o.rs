//! Table O — canonical opened junction (R3/M6, `DEVPLAN-R3.md` §5.5). One row
//! per `O`. Splits the opening path out of the old union Table F and, crucially,
//! **range-checks the opened region** so an accepted row is exactly a canonical
//! left-aligned `depth`-bit prefix (soundness lemma S5; finding §4: F openings
//! never proved canonical regions).
//!
//! Local constraints (the S5 arithmetization, all `check_constraints`-testable):
//! one-hot boundary limb `q`, `depth = limb_start(q) + r_off`, region limbs as
//! linear digit reconstructions, zero below the boundary limb, and
//! `region[q] = 2·pow_b·H` with `H < 2^r_off`. Bus-backed: the 26 region digits
//! and 3 `H` digits (range, Table R), `pow_b = 2^(W−r_off−1)` (pow2, Table P),
//! the node prefix / children permutations (p2ff/p2term, Table B), and the
//! parent tuple send (Table A). Full balance is the M7 end-to-end test.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_hash::DOMAIN_NODE;
use rsmt_witness::r3plan::R3Open;

use crate::cols::{cast, width_of};

const LIMBS: usize = 9;

/// MSB position of each limb's top bit.
const LIMB_START: [u32; LIMBS] = [0, 30, 60, 90, 120, 150, 180, 210, 240];
/// Radix-1024 digit widths for the 26 region digits: `[10,10,10]×8 ++ [10,6]`.
const DIGIT_WIDTH: [u32; 26] = {
    let mut w = [10u32; 26];
    w[25] = 6;
    w
};
const fn limb_digits(j: usize) -> usize {
    if j < 8 { 3 } else { 2 }
}
const fn limb_digit_offset(j: usize) -> usize {
    if j < 8 { 3 * j } else { 24 }
}

/// Main columns (89).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct OCols<T> {
    pub a_row_idx: T,
    pub depth: T,
    pub region_digits: [T; 26],
    pub q: [T; LIMBS],
    pub r_off: T,
    pub pow_b: T,
    pub h_digits: [T; 3],
    pub h_u: [T; 3],
    pub h_s: T,
    pub width_h: [T; 3],
    pub left_digest: [T; 8],
    pub right_digest: [T; 8],
    pub prefix_mid: [T; 16],
    pub digest: [T; 8],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct OPrepCols<T> {
    pub is_real: T,
}

pub const TABLE_O_WIDTH: usize = width_of::<OCols<u8>>();
pub const TABLE_O_PREP_WIDTH: usize = width_of::<OPrepCols<u8>>();

const _: () = assert!(TABLE_O_WIDTH == 89);

#[derive(Clone)]
pub struct TableOAir {
    pub padded_height: usize,
    pub real_rows: usize,
    pub num_lookups: usize,
}

impl TableOAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableOAir {
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
            main_width: TABLE_O_WIDTH,
            preprocessed_width: TABLE_O_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let pl = sb.preprocessed().current_slice();
        let is_real: SE<F> = pl[0].into();

        // Offsets into the main row (must match OCols).
        let o_region = 2usize;
        let o_q = o_region + 26; // 28
        let o_roff = o_q + 9; // 37
        let o_powb = o_roff + 1; // 38
        let o_hdig = o_powb + 1; // 39
        let o_widthh = o_hdig + 3 + 3 + 1; // h_digits(3)+h_u(3)+h_s(1) → 46
        let o_left = o_widthh + 3; // 49
        let o_right = o_left + 8; // 57
        let o_mid = o_right + 8; // 65
        let o_digest = o_mid + 16; // 81

        let region_limb = |j: usize| -> SE<F> {
            let off = o_region + limb_digit_offset(j);
            let mut acc = SE::<F>::ZERO;
            let mut w = F::ONE;
            for i in 0..limb_digits(j) {
                acc += SE::<F>::from(ml[off + i]) * SE::<F>::from(w);
                w *= F::from_u32(1024);
            }
            acc
        };

        let mut lookups = Vec::new();

        // range: 26 region digits (fixed width) + 3 H digits (variable width_h).
        for k in 0..26 {
            let tuple = vec![
                SE::<F>::from(F::from_u32(DIGIT_WIDTH[k])),
                SE::<F>::from(ml[o_region + k]),
            ];
            lookups.push(p3_lookup::LookupAir::register_lookup(
                self,
                Kind::Global(crate::table_r::BUS_RANGE_NAME.to_string()),
                &[(tuple, is_real.clone(), Direction::Receive)],
            ));
        }
        for i in 0..3 {
            let tuple = vec![
                SE::<F>::from(ml[o_widthh + i]),
                SE::<F>::from(ml[o_hdig + i]),
            ];
            lookups.push(p3_lookup::LookupAir::register_lookup(
                self,
                Kind::Global(crate::table_r::BUS_RANGE_NAME.to_string()),
                &[(tuple, is_real.clone(), Direction::Receive)],
            ));
        }

        // pow2: (W(q) − r_off − 1, pow_b), W(q) = 30 − 14·q[8].
        let w_q: SE<F> = SE::<F>::from(F::from_u32(30))
            - SE::<F>::from(F::from_u32(14)) * SE::<F>::from(ml[o_q + 8]);
        let exponent = w_q - SE::<F>::from(ml[o_roff]) - SE::<F>::from(F::ONE);
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_f::BUS_POW2_NAME.to_string()),
            &[(
                vec![exponent, SE::<F>::from(ml[o_powb])],
                is_real.clone(),
                Direction::Receive,
            )],
        ));

        // p2ff: node prefix input [DOMAIN_NODE, depth, region0..8, 0×5] → mid.
        let mut ff: Vec<SE<F>> = Vec::with_capacity(32);
        ff.push(SE::<F>::from(F::from_u32(DOMAIN_NODE)));
        ff.push(SE::<F>::from(ml[1])); // depth
        for j in 0..LIMBS {
            ff.push(region_limb(j));
        }
        for _ in 11..16 {
            ff.push(SE::<F>::ZERO);
        }
        for i in 0..16 {
            ff.push(SE::<F>::from(ml[o_mid + i]));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_b::BUS_P2FF_NAME.to_string()),
            &[(ff, is_real.clone(), Direction::Receive)],
        ));

        // p2term: children input mid + left‖right → digest[8].
        let mut term: Vec<SE<F>> = Vec::with_capacity(24);
        for i in 0..16 {
            let inj = if i < 8 {
                SE::<F>::from(ml[o_left + i])
            } else {
                SE::<F>::from(ml[o_right + (i - 8)])
            };
            term.push(SE::<F>::from(ml[o_mid + i]) + inj);
        }
        for i in 0..8 {
            term.push(SE::<F>::from(ml[o_digest + i]));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_b::BUS_P2TERM_NAME.to_string()),
            &[(term, is_real.clone(), Direction::Receive)],
        ));

        // parent send: (a_row_idx, digest[8], digest[8], 0, depth, region[9],
        // subtree_start=a_row_idx). R3 drops `nhon` (§5.8).
        let mut parent: Vec<SE<F>> = vec![SE::<F>::from(ml[0])];
        for i in 0..8 {
            parent.push(SE::<F>::from(ml[o_digest + i])); // old = digest
        }
        for i in 0..8 {
            parent.push(SE::<F>::from(ml[o_digest + i])); // new = digest
        }
        parent.push(SE::<F>::ZERO); // old_is_none = 0 (present)
        parent.push(SE::<F>::from(ml[1])); // delta = depth
        for j in 0..LIMBS {
            parent.push(region_limb(j)); // rho = region
        }
        parent.push(SE::<F>::from(ml[0])); // subtree_start = a_row_idx
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_PARENT_NAME.to_string()),
            &[(parent, is_real.clone(), Direction::Send)],
        ));

        lookups
    }
}

pub const BUS_PARENT_NAME: &str = "parent";

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableOAir {
    fn width(&self) -> usize {
        TABLE_O_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(self.padded_height * TABLE_O_PREP_WIDTH);
        for i in 0..self.padded_height {
            data.push(F::from_bool(i < self.real_rows));
        }
        Some(RowMajorMatrix::new(data, TABLE_O_PREP_WIDTH))
    }

    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for TableOAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let (c, is_real): (OCols<AB::Var>, AB::Var) = {
            let main = builder.main();
            let prep = builder.preprocessed();
            let pl: &OPrepCols<AB::Var> = cast(prep.current_slice());
            (*cast(main.current_slice()), pl.is_real)
        };
        let one = AB::Expr::ONE;
        let e = |v: AB::Var| -> AB::Expr { v.into() };
        let is_real = e(is_real);

        // Padding hygiene.
        let not_real = one.clone() - is_real.clone();
        let all = [
            &[c.a_row_idx, c.depth, c.r_off, c.pow_b, c.h_s][..],
            &c.region_digits[..],
            &c.q[..],
            &c.h_digits[..],
            &c.h_u[..],
            &c.width_h[..],
            &c.left_digest[..],
            &c.right_digest[..],
            &c.prefix_mid[..],
            &c.digest[..],
        ];
        for slice in all {
            for &cell in slice {
                builder.assert_zero(not_real.clone() * e(cell));
            }
        }

        // q one-hot (real) + booleanity.
        for j in 0..LIMBS {
            builder.assert_zero(e(c.q[j]) * (e(c.q[j]) - one.clone()));
        }
        let q_sum: AB::Expr = (0..LIMBS).map(|j| e(c.q[j])).sum();
        builder.assert_zero(is_real.clone() * (q_sum - one.clone()));

        // h_u one-hot (real) + booleanity.
        for i in 0..3 {
            builder.assert_zero(e(c.h_u[i]) * (e(c.h_u[i]) - one.clone()));
        }
        let hu_sum: AB::Expr = (0..3).map(|i| e(c.h_u[i])).sum();
        builder.assert_zero(is_real.clone() * (hu_sum - one.clone()));

        // depth = Σ limb_start·q + r_off.
        let start_dot_q: AB::Expr = (0..LIMBS)
            .map(|j| e(c.q[j]) * AB::Expr::from_u32(LIMB_START[j]))
            .sum();
        builder.assert_zero(is_real.clone() * (e(c.depth) - start_dot_q - e(c.r_off)));

        // Region limb reconstruction (radix 1024).
        let region_limb = |j: usize| -> AB::Expr {
            let n = limb_digits(j);
            let off = limb_digit_offset(j);
            let mut acc = AB::Expr::ZERO;
            let mut w = AB::Expr::ONE;
            for i in 0..n {
                acc += e(c.region_digits[off + i]) * w.clone();
                w *= AB::Expr::from_u32(1024);
            }
            acc
        };

        // Zero strictly below the boundary limb: for j > q, region_limb(j) = 0.
        // below(j) = Σ_{k<j} q[k] = 1 iff q < j.
        for j in 0..LIMBS {
            let below: AB::Expr = (0..j).map(|k| e(c.q[k])).sum();
            builder.assert_zero(below * region_limb(j));
        }

        // Boundary limb value = 2·pow_b·H, H = Σ h_digits·1024^i.
        let region_q: AB::Expr = (0..LIMBS).map(|j| e(c.q[j]) * region_limb(j)).sum();
        let h_val: AB::Expr = e(c.h_digits[0])
            + e(c.h_digits[1]) * AB::Expr::from_u32(1024)
            + e(c.h_digits[2]) * AB::Expr::from_u32(1024 * 1024);
        builder
            .assert_zero(is_real.clone() * (region_q - AB::Expr::from_u32(2) * e(c.pow_b) * h_val));

        // r_off = 10·h_r + h_s, h_r = Σ i·h_u[i].
        let h_r: AB::Expr = (0..3)
            .map(|i| e(c.h_u[i]) * AB::Expr::from_u32(i as u32))
            .sum();
        builder
            .assert_zero(is_real.clone() * (e(c.r_off) - AB::Expr::from_u32(10) * h_r - e(c.h_s)));

        // width_h[i] = 10·[i<h_r] + h_s·h_u[i]. lt_h(i) = Σ_{k>i} h_u[k].
        for i in 0..3 {
            let lt_h: AB::Expr = ((i + 1)..3).map(|k| e(c.h_u[k])).sum();
            let wh = AB::Expr::from_u32(10) * lt_h + e(c.h_s) * e(c.h_u[i]);
            builder.assert_zero(is_real.clone() * (e(c.width_h[i]) - wh));
        }
    }
}

// -- trace generation -------------------------------------------------------

/// Build Table O's main trace from the R3 opening plan (one row per opening).
pub fn build_trace(opens: &[R3Open]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = opens.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_O_WIDTH);
    let z = BabyBear::ZERO;
    for o in opens {
        let h_r = (o.r_off / 10) as usize;
        let h_s = o.r_off % 10;
        data.push(BabyBear::from_u32(o.a_row_idx));
        data.push(BabyBear::from_u32(o.depth as u32));
        for &d in &o.region_digits {
            data.push(BabyBear::from_u32(d));
        }
        for j in 0..LIMBS {
            data.push(BabyBear::from_bool(j == o.q));
        }
        data.push(BabyBear::from_u32(o.r_off as u32));
        data.push(BabyBear::from_u32(o.pow_b));
        for &d in &o.h_digits {
            data.push(BabyBear::from_u32(d));
        }
        for i in 0..3 {
            data.push(BabyBear::from_bool(o.h_u[i]));
        }
        data.push(BabyBear::from_u32(h_s as u32));
        for i in 0..3 {
            let wh = if i < h_r {
                10
            } else if i == h_r {
                h_s as u32
            } else {
                0
            };
            data.push(BabyBear::from_u32(wh));
        }
        data.extend_from_slice(&o.left_digest);
        data.extend_from_slice(&o.right_digest);
        data.extend_from_slice(&o.prefix_mid);
        data.extend_from_slice(&o.digest);
    }
    for _ in real..height {
        data.extend(std::iter::repeat_n(z, TABLE_O_WIDTH));
    }
    (RowMajorMatrix::new(data, TABLE_O_WIDTH), real, height)
}

#[cfg(test)]
mod tests;
