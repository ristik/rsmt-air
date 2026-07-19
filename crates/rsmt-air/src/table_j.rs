//! Table J — joins only (R3/M5, `DEVPLAN-R3.md` §5.4). Splits the join path out
//! of the union Table F: every row is a junction, so there is no `is_open`
//! selector and no cross-kind zeroing. The coherence, four-way old-state, and
//! node-hash logic is a faithful port of F's (working, tested) join `eval`
//! (soundness lemmas S2/S3/S6/S7). The parent tuple **drops** F's `nhon` (§5.8).
//!
//! R10 coherence (D13): a shared prefix `H` with `p[q] = 2·pow_b·H`, constant
//! side bits (`β_l = 0`, `β_r = 1`), and radix-1024 digit decompositions of `H`
//! (`< 2^r`) and each child tail `L` (`< 2^k`), so `ρ_l[q] = p[q] + L_l` and
//! `ρ_r[q] = p[q] + pow_b + L_r`. Materialized `width_r/width_k` keep the
//! range-bus tuple degree 1.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_core::LIMBS;
use rsmt_hash::{DOMAIN_NODE, STATE_WIDTH};
use rsmt_witness::r3plan::R3Join;

use crate::cols::{cast, width_of};

const DW: usize = 8;
const LIMB_START: [u32; LIMBS] = [0, 30, 60, 90, 120, 150, 180, 210, 240];

/// Main columns (142), field order matching the old Table F join layout.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct JCols<T> {
    pub parent_row_idx: T,
    pub ls: T,
    pub rs: T,
    pub depth: T,
    pub region: [T; LIMBS],
    pub q: [T; LIMBS],
    pub r_off: T,
    pub pow_b: T,
    pub h: T,
    pub h_d: [T; 3],
    pub u_r: [T; 3],
    pub s_r: T,
    pub u_k: [T; 3],
    pub s_k: T,
    pub l_old: [T; DW],
    pub l_new: [T; DW],
    pub l_none: T,
    pub has_l: T,
    pub l_delta: T,
    pub l_rho: [T; LIMBS],
    pub l_l: T,
    pub l_l_d: [T; 3],
    pub r_old: [T; DW],
    pub r_new: [T; DW],
    pub r_none: T,
    pub has_r: T,
    pub r_delta: T,
    pub r_rho: [T; LIMBS],
    pub r_l: T,
    pub r_l_d: [T; 3],
    pub b01: T,
    pub b10: T,
    pub b11: T,
    pub parent_none: T,
    pub parent_old: [T; DW],
    pub parent_new: [T; DW],
    pub width_r: [T; 3],
    pub width_k: [T; 3],
    pub mid: [T; STATE_WIDTH],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct JPrepCols<T> {
    pub is_real: T,
}

pub const TABLE_J_WIDTH: usize = width_of::<JCols<u8>>();
pub const TABLE_J_PREP_WIDTH: usize = width_of::<JPrepCols<u8>>();

const _: () = assert!(TABLE_J_WIDTH == 142);

#[derive(Clone)]
pub struct TableJAir {
    pub padded_height: usize,
    pub real_rows: usize,
    pub num_lookups: usize,
}

impl TableJAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableJAir {
    fn width(&self) -> usize {
        TABLE_J_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut data = Vec::with_capacity(self.padded_height * TABLE_J_PREP_WIDTH);
        for i in 0..self.padded_height {
            data.push(F::from_bool(i < self.real_rows));
        }
        Some(RowMajorMatrix::new(data, TABLE_J_PREP_WIDTH))
    }

    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for TableJAir
where
    AB::F: Send,
{
    #[allow(clippy::type_complexity)]
    fn eval(&self, builder: &mut AB) {
        let (c, is_real, row): (JCols<AB::Var>, AB::Var, Vec<AB::Var>) = {
            let main = builder.main();
            let prep = builder.preprocessed();
            let pl: &JPrepCols<AB::Var> = cast(prep.current_slice());
            (
                *cast(main.current_slice()),
                pl.is_real,
                main.current_slice().to_vec(),
            )
        };
        let one = AB::Expr::ONE;
        let e = |v: AB::Var| -> AB::Expr { v.into() };
        let is_real = e(is_real);

        // padding hygiene.
        let not_real = one.clone() - is_real.clone();
        for &cell in &row {
            builder.assert_zero(not_real.clone() * e(cell));
        }

        // booleanity.
        for b in [
            c.l_none,
            c.r_none,
            c.has_l,
            c.has_r,
            c.b01,
            c.b10,
            c.b11,
            c.parent_none,
        ] {
            builder.assert_zero(e(b) * (e(b) - one.clone()));
        }
        for j in 0..LIMBS {
            builder.assert_zero(e(c.q[j]) * (e(c.q[j]) - one.clone()));
        }
        for i in 0..3 {
            builder.assert_zero(e(c.u_r[i]) * (e(c.u_r[i]) - one.clone()));
            builder.assert_zero(e(c.u_k[i]) * (e(c.u_k[i]) - one.clone()));
        }

        // one-hot q / u_r / u_k on real rows.
        let q_sum: AB::Expr = (0..LIMBS).map(|j| e(c.q[j])).sum();
        builder.assert_zero(q_sum - is_real.clone());
        let ur_sum: AB::Expr = (0..3).map(|i| e(c.u_r[i])).sum();
        let uk_sum: AB::Expr = (0..3).map(|i| e(c.u_k[i])).sum();
        builder.assert_zero(is_real.clone() * (ur_sum - one.clone()));
        builder.assert_zero(is_real.clone() * (uk_sum - one.clone()));

        // depth = Σ start·q + r_off.
        let start_dot_q: AB::Expr = (0..LIMBS)
            .map(|j| e(c.q[j]) * AB::Expr::from_u32(LIMB_START[j]))
            .sum();
        builder.assert_zero(is_real.clone() * (e(c.depth) - start_dot_q - e(c.r_off)));

        let lt = |j: usize| -> AB::Expr { (j + 1..LIMBS).map(|k| e(c.q[k])).sum() };
        let gt = |j: usize| -> AB::Expr { (0..j).map(|k| e(c.q[k])).sum() };

        // region zero strictly below the boundary limb.
        for j in 0..LIMBS {
            builder.assert_zero(gt(j) * e(c.region[j]));
        }

        let sel = |cols: &[AB::Var; LIMBS]| -> AB::Expr {
            (0..LIMBS).map(|j| e(c.q[j]) * e(cols[j])).sum()
        };
        let region_q = sel(&c.region);
        let l_rho_q = sel(&c.l_rho);
        let r_rho_q = sel(&c.r_rho);

        // digit reconstruction (radix 1024).
        let r1024 = |d: &[AB::Var; 3]| -> AB::Expr {
            e(d[0]) + e(d[1]) * AB::Expr::from_u32(1 << 10) + e(d[2]) * AB::Expr::from_u32(1 << 20)
        };
        builder.assert_zero(is_real.clone() * (e(c.h) - r1024(&c.h_d)));
        builder.assert_zero(e(c.has_l) * (e(c.l_l) - r1024(&c.l_l_d)));
        builder.assert_zero(e(c.has_r) * (e(c.r_l) - r1024(&c.r_l_d)));

        // r_off = 10·h_r + s_r; k = W − r_off − 1 = 10·h_k + s_k; W = 30 − 14·q[8].
        let h_r: AB::Expr = (0..3)
            .map(|i| e(c.u_r[i]) * AB::Expr::from_u32(i as u32))
            .sum();
        let h_k: AB::Expr = (0..3)
            .map(|i| e(c.u_k[i]) * AB::Expr::from_u32(i as u32))
            .sum();
        builder
            .assert_zero(is_real.clone() * (e(c.r_off) - AB::Expr::from_u32(10) * h_r - e(c.s_r)));
        let w = AB::Expr::from_u32(30) - AB::Expr::from_u32(14) * e(c.q[8]);
        let k = w - e(c.r_off) - one.clone();
        builder.assert_zero(is_real.clone() * (k - AB::Expr::from_u32(10) * h_k - e(c.s_k)));

        // high digits zero (above the boundary digit).
        let gt_r = |i: usize| -> AB::Expr { (0..i).map(|j| e(c.u_r[j])).sum() };
        let gt_k = |i: usize| -> AB::Expr { (0..i).map(|j| e(c.u_k[j])).sum() };
        for i in 1..3 {
            builder.assert_zero(e(c.h_d[i]) * gt_r(i));
            builder.assert_zero(e(c.has_l) * e(c.l_l_d[i]) * gt_k(i));
            builder.assert_zero(e(c.has_r) * e(c.r_l_d[i]) * gt_k(i));
        }

        // materialized digit widths (keep range-bus tuple degree 1).
        let lt_ru = |i: usize| -> AB::Expr { (i + 1..3).map(|j| e(c.u_r[j])).sum() };
        let lt_ku = |i: usize| -> AB::Expr { (i + 1..3).map(|j| e(c.u_k[j])).sum() };
        for i in 0..3 {
            let wr = AB::Expr::from_u32(10) * lt_ru(i) + e(c.s_r) * e(c.u_r[i]);
            let wk = AB::Expr::from_u32(10) * lt_ku(i) + e(c.s_k) * e(c.u_k[i]);
            builder.assert_zero(is_real.clone() * (e(c.width_r[i]) - wr));
            builder.assert_zero(is_real.clone() * (e(c.width_k[i]) - wk));
        }

        // case bits.
        let l_none = e(c.l_none);
        let r_none = e(c.r_none);
        builder.assert_zero(is_real.clone() * (e(c.parent_none) - l_none.clone() * r_none.clone()));
        builder.assert_zero(
            is_real.clone() * (e(c.b01) - l_none.clone() * (one.clone() - r_none.clone())),
        );
        builder.assert_zero(
            is_real.clone() * (e(c.b10) - (one.clone() - l_none.clone()) * r_none.clone()),
        );
        builder.assert_zero(
            is_real.clone() * (e(c.b11) - (one.clone() - l_none) * (one.clone() - r_none)),
        );

        // four-way old-state (b00/b01/b10 local; b11 via node hash on Bus 2).
        for j in 0..DW {
            builder.assert_zero(e(c.parent_none) * e(c.parent_old[j]));
            builder.assert_zero(e(c.b01) * (e(c.parent_old[j]) - e(c.r_old[j])));
            builder.assert_zero(e(c.b10) * (e(c.parent_old[j]) - e(c.l_old[j])));
        }

        // confinement: at least one child advised; both advised for a new (b11=0) junction.
        builder
            .assert_zero(is_real.clone() * (one.clone() - e(c.has_l)) * (one.clone() - e(c.has_r)));
        builder.assert_zero(
            is_real.clone()
                * (one.clone() - e(c.b11))
                * (AB::Expr::from_u32(2) - e(c.has_l) - e(c.has_r)),
        );

        // R10 boundary equations.
        let two_pb_h = AB::Expr::from_u32(2) * e(c.pow_b) * e(c.h);
        builder.assert_zero(is_real.clone() * (region_q - two_pb_h.clone()));
        builder.assert_zero(e(c.has_l) * (l_rho_q - two_pb_h.clone() - e(c.l_l)));
        builder.assert_zero(e(c.has_r) * (r_rho_q - two_pb_h - e(c.pow_b) - e(c.r_l)));

        // whole-limb prefix equalities ρ_x[j] = region[j] for j above the boundary.
        for j in 0..LIMBS {
            builder.assert_zero(e(c.has_l) * lt(j) * (e(c.l_rho[j]) - e(c.region[j])));
            builder.assert_zero(e(c.has_r) * lt(j) * (e(c.r_rho[j]) - e(c.region[j])));
        }
    }
}

// Column indices into JCols (track the field order; equal to the old F CI_*).
const CI_PARENT_IDX: usize = 0;
const CI_LS: usize = 1;
const CI_RS: usize = 2;
const CI_DEPTH: usize = 3;
const CI_REGION: usize = 4;
const CI_Q8: usize = 21;
const CI_R_OFF: usize = 22;
const CI_POW_B: usize = 23;
const CI_H_D: usize = 25;
const CI_L_OLD: usize = 36;
const CI_L_NEW: usize = 44;
const CI_L_NONE: usize = 52;
const CI_HAS_L: usize = 53;
const CI_L_DELTA: usize = 54;
const CI_L_RHO: usize = 55;
const CI_L_L_D: usize = 65;
const CI_R_OLD: usize = 68;
const CI_R_NEW: usize = 76;
const CI_R_NONE: usize = 84;
const CI_HAS_R: usize = 85;
const CI_R_DELTA: usize = 86;
const CI_R_RHO: usize = 87;
const CI_R_L_D: usize = 97;
const CI_B11: usize = 102;
const CI_PARENT_NONE: usize = 103;
const CI_PARENT_OLD: usize = 104;
const CI_PARENT_NEW: usize = 112;
const CI_WIDTH_R: usize = 120;
const CI_WIDTH_K: usize = 123;
const CI_MID: usize = 126;

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableJAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        use p3_air::AirLayout;
        use p3_air::symbolic::{BaseLeaf, SymbolicAirBuilder, SymbolicExpression};
        use p3_lookup::{Direction, Kind};

        use crate::table_ar::BUS_TREE_NAME;
        use crate::table_b::{BUS_P2FF_NAME, BUS_P2TERM_NAME};
        use crate::table_o::BUS_PARENT_NAME;
        use crate::table_p::BUS_POW2_NAME;
        use crate::table_r::BUS_RANGE_NAME;

        type SE<F> = SymbolicExpression<F>;
        self.num_lookups = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: TABLE_J_WIDTH,
            preprocessed_width: TABLE_J_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let is_real: SE<F> = prep.current_slice()[0].into();

        let konst = |v: u32| SE::<F>::Leaf(BaseLeaf::Constant(F::from_u32(v)));
        let var = |i: usize| -> SE<F> { ml[i].into() };

        let mut lookups = Vec::new();
        let mut recv = |this: &mut Self, name: &str, tuple: Vec<SE<F>>, mult: SE<F>| {
            lookups.push(p3_lookup::LookupAir::register_lookup(
                this,
                Kind::Global(name.to_string()),
                &[(tuple, mult, Direction::Receive)],
            ));
        };

        // range: depth (every row); H digits; per advised child the L digits + gap.
        recv(
            self,
            BUS_RANGE_NAME,
            vec![konst(8), var(CI_DEPTH)],
            is_real.clone(),
        );
        for i in 0..3 {
            recv(
                self,
                BUS_RANGE_NAME,
                vec![var(CI_WIDTH_R + i), var(CI_H_D + i)],
                is_real.clone(),
            );
        }
        for i in 0..3 {
            recv(
                self,
                BUS_RANGE_NAME,
                vec![var(CI_WIDTH_K + i), var(CI_L_L_D + i)],
                var(CI_HAS_L),
            );
        }
        recv(
            self,
            BUS_RANGE_NAME,
            vec![konst(8), var(CI_L_DELTA) - var(CI_DEPTH) - konst(1)],
            var(CI_HAS_L),
        );
        for i in 0..3 {
            recv(
                self,
                BUS_RANGE_NAME,
                vec![var(CI_WIDTH_K + i), var(CI_R_L_D + i)],
                var(CI_HAS_R),
            );
        }
        recv(
            self,
            BUS_RANGE_NAME,
            vec![konst(8), var(CI_R_DELTA) - var(CI_DEPTH) - konst(1)],
            var(CI_HAS_R),
        );

        // pow2: one pow_b receive per join, exponent k = W − r_off − 1.
        let ek = konst(30) - konst(14) * var(CI_Q8) - var(CI_R_OFF) - konst(1);
        recv(
            self,
            BUS_POW2_NAME,
            vec![ek, var(CI_POW_B)],
            is_real.clone(),
        );

        // tree: receive both children (right key = parent−1, left key = rs−1).
        let child = |key: SE<F>,
                     sst: SE<F>,
                     old: usize,
                     new: usize,
                     none: usize,
                     has: usize,
                     delta: usize,
                     rho: usize|
         -> Vec<SE<F>> {
            let mut t = vec![key, sst];
            for j in 0..8 {
                t.push(var(old + j));
            }
            for j in 0..8 {
                t.push(var(new + j));
            }
            t.push(var(none));
            t.push(var(has));
            t.push(var(delta));
            for j in 0..LIMBS {
                t.push(var(rho + j));
            }
            t
        };
        recv(
            self,
            BUS_TREE_NAME,
            child(
                var(CI_RS) - konst(1),
                var(CI_LS),
                CI_L_OLD,
                CI_L_NEW,
                CI_L_NONE,
                CI_HAS_L,
                CI_L_DELTA,
                CI_L_RHO,
            ),
            is_real.clone(),
        );
        recv(
            self,
            BUS_TREE_NAME,
            child(
                var(CI_PARENT_IDX) - konst(1),
                var(CI_RS),
                CI_R_OLD,
                CI_R_NEW,
                CI_R_NONE,
                CI_HAS_R,
                CI_R_DELTA,
                CI_R_RHO,
            ),
            is_real.clone(),
        );

        // p2ff: node prefix (input[16], mid[16]).
        let mut pre_in: Vec<SE<F>> = vec![konst(DOMAIN_NODE), var(CI_DEPTH)];
        for j in 0..LIMBS {
            pre_in.push(var(CI_REGION + j));
        }
        for _ in 0..5 {
            pre_in.push(konst(0));
        }
        for j in 0..16 {
            pre_in.push(var(CI_MID + j));
        }
        recv(self, BUS_P2FF_NAME, pre_in, is_real.clone());

        // p2term: children blocks (input[16], digest[8]); old only iff b11.
        let children = |lo: usize, ro: usize, digest: usize| -> Vec<SE<F>> {
            let mut t: Vec<SE<F>> = Vec::with_capacity(24);
            for j in 0..8 {
                t.push(var(CI_MID + j) + var(lo + j));
            }
            for j in 0..8 {
                t.push(var(CI_MID + 8 + j) + var(ro + j));
            }
            for j in 0..8 {
                t.push(var(digest + j));
            }
            t
        };
        recv(
            self,
            BUS_P2TERM_NAME,
            children(CI_L_NEW, CI_R_NEW, CI_PARENT_NEW),
            is_real.clone(),
        );
        recv(
            self,
            BUS_P2TERM_NAME,
            children(CI_L_OLD, CI_R_OLD, CI_PARENT_OLD),
            var(CI_B11),
        );

        // parent send (R3 tuple, NO nhon): (row_idx, old[8], new[8], none, depth,
        // region[9], subtree_start=ls). Pushed last so `recv`'s borrow has ended.
        let mut ptuple: Vec<SE<F>> = vec![var(CI_PARENT_IDX)];
        for j in 0..8 {
            ptuple.push(var(CI_PARENT_OLD + j));
        }
        for j in 0..8 {
            ptuple.push(var(CI_PARENT_NEW + j));
        }
        ptuple.push(var(CI_PARENT_NONE));
        ptuple.push(var(CI_DEPTH));
        for j in 0..LIMBS {
            ptuple.push(var(CI_REGION + j));
        }
        ptuple.push(var(CI_LS));
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_PARENT_NAME.to_string()),
            &[(ptuple, is_real, Direction::Send)],
        ));

        lookups
    }
}

// -- trace generation -------------------------------------------------------

/// Build Table J's main trace from the R3 join plan (one row per junction).
pub fn build_trace(joins: &[R3Join]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = joins.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_J_WIDTH);
    let f = BabyBear::from_u32;
    let fb = BabyBear::from_bool;

    for j in joins {
        let h_r = j.u_r.iter().position(|&b| b).unwrap_or(0);
        let h_k = j.u_k.iter().position(|&b| b).unwrap_or(0);
        let width = |lt_hi: usize, s: u16, u: &[bool; 3], i: usize| -> u32 {
            if i < lt_hi {
                10
            } else if u[i] {
                s as u32
            } else {
                0
            }
        };
        data.push(f(j.parent_row_idx));
        data.push(f(j.ls));
        data.push(f(j.rs));
        data.push(f(j.depth as u32));
        for &v in &j.region {
            data.push(f(v));
        }
        for x in 0..LIMBS {
            data.push(fb(x == j.q));
        }
        data.push(f(j.r_off as u32));
        data.push(f(j.pow_b));
        data.push(f(j.h));
        for &v in &j.h_digits {
            data.push(f(v));
        }
        for &b in &j.u_r {
            data.push(fb(b));
        }
        data.push(f(j.s_r as u32));
        for &b in &j.u_k {
            data.push(fb(b));
        }
        data.push(f(j.s_k as u32));
        // left child
        data.extend_from_slice(&j.l_old);
        data.extend_from_slice(&j.l_new);
        data.push(fb(j.l_none));
        data.push(fb(j.child_l.has));
        data.push(f(j.child_l.delta as u32));
        for &v in &j.child_l.rho {
            data.push(f(v));
        }
        data.push(f(j.child_l.l));
        for &v in &j.child_l.l_digits {
            data.push(f(v));
        }
        // right child
        data.extend_from_slice(&j.r_old);
        data.extend_from_slice(&j.r_new);
        data.push(fb(j.r_none));
        data.push(fb(j.child_r.has));
        data.push(f(j.child_r.delta as u32));
        for &v in &j.child_r.rho {
            data.push(f(v));
        }
        data.push(f(j.child_r.l));
        for &v in &j.child_r.l_digits {
            data.push(f(v));
        }
        // case bits
        data.push(fb(j.l_none && !j.r_none)); // b01
        data.push(fb(!j.l_none && j.r_none)); // b10
        data.push(fb(j.b11));
        data.push(fb(j.parent_none));
        data.extend_from_slice(&j.parent_old);
        data.extend_from_slice(&j.parent_new);
        for i in 0..3 {
            data.push(f(width(h_r, j.s_r, &j.u_r, i)));
        }
        for i in 0..3 {
            data.push(f(width(h_k, j.s_k, &j.u_k, i)));
        }
        data.extend_from_slice(&j.mid);
    }
    for _ in real..height {
        data.extend(std::iter::repeat_n(BabyBear::ZERO, TABLE_J_WIDTH));
    }
    (RowMajorMatrix::new(data, TABLE_J_WIDTH), real, height)
}

#[cfg(test)]
mod tests;
