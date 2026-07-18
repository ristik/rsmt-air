//! Table F — junctions: join + opening rows (DEVPLAN R2, D13).
//!
//! Union layout, segmented join-then-open (`is_join`/`is_open` preprocessed).
//! **R10 coherence:** per join a shared prefix `H`, child tails `L_l/L_r`, one
//! `pow_b = 2^k` power (`pow_a = 2·pow_b` derived), and radix-1024 digit
//! decompositions of `H` (`< 2^r`) and `L` (`< 2^k`). The boundary equations
//! `p[q] = 2·pow_b·H`, `ρ_l[q] = p[q] + L_l`, `ρ_r[q] = p[q] + pow_b + L_r`
//! force the side bit (`β_l = 0`, `β_r = 1` are constant). Local (degree ≤ 3):
//! reconstructions, boundary equations, one-hot digit selectors + high-digits-
//! zero, case algebra, four-way pass-through, prefix equalities, locality.
//!
//! Bus-backed (M4): `pow_b` (Bus 7, Table P — one per join); the digit range
//! bounds and `gap`/`depth` (range bus, Table R); the digest bindings (Bus 1/2/3).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_core::{Key, LIMBS};
use rsmt_hash::{DIGEST_WIDTH, DOMAIN_NODE};
use rsmt_witness::{FJoin, FOpen, TracePlan};

use crate::cols::{cast, width_of};

const DW: usize = DIGEST_WIDTH; // 8

/// MSB position of each limb's top bit.
const LIMB_START: [u32; LIMBS] = [0, 30, 60, 90, 120, 150, 180, 210, 240];

pub const BUS_POW2_NAME: &str = "pow2";

/// Main columns for a Table F row (union of join and opening).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FCols<T> {
    pub parent_row_idx: T,
    /// D19 post-order subtree starts: `ls` = left child's start (= this join's
    /// own start, sent on Bus 3); `rs` = right child's start. The left child
    /// row is `rs − 1`, the right child row `parent_row_idx − 1` — both Bus-1
    /// receive keys, so neither child pointer is an unconstrained witness.
    pub ls: T,
    pub rs: T,
    pub depth: T,
    pub region: [T; LIMBS],
    // shared R10 coherence
    pub q: [T; LIMBS],
    pub r_off: T,
    pub pow_b: T,
    pub h: T,
    pub h_d: [T; 3],
    pub u_r: [T; 3],
    pub s_r: T,
    pub u_k: [T; 3],
    pub s_k: T,
    // left child
    pub l_old: [T; DW],
    pub l_new: [T; DW], // opening: c_l
    pub l_none: T,
    pub has_l: T,
    pub l_delta: T,
    pub l_rho: [T; LIMBS],
    pub l_l: T,
    pub l_l_d: [T; 3],
    // right child
    pub r_old: [T; DW],
    pub r_new: [T; DW], // opening: c_r
    pub r_none: T,
    pub has_r: T,
    pub r_delta: T,
    pub r_rho: [T; LIMBS],
    pub r_l: T,
    pub r_l_d: [T; 3],
    // case bits
    pub b01: T,
    pub b10: T,
    pub b11: T,
    pub parent_none: T,
    // parent tuple
    pub parent_old: [T; DW],
    pub parent_new: [T; DW], // opening: digest
    // materialized digit widths (keep the range-bus LogUp tuple degree 1):
    // width_r[i] = 10·[i<h_r] + s_r·u_r[i]; width_k[i] likewise for k.
    pub width_r: [T; 3],
    pub width_k: [T; 3],
    // Shared node-sponge prefix output `mid[16]` — feed-forward (D17 mode = 1),
    // so its full state is on Bus 2. The two children blocks are terminal
    // (mode = 0): their digest is taken directly from `parent_new`/`parent_old`
    // (which the Bus-2 receive thereby binds to the real Poseidon2 output), so
    // no separate output columns are carried.
    pub mid: [T; 16],
}

/// Preprocessed columns (3): the segmented kind selectors + realness.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FPrepCols<T> {
    pub is_join: T,
    pub is_open: T,
    pub is_real: T,
}

pub const TABLE_F_WIDTH: usize = width_of::<FCols<u8>>();
pub const TABLE_F_PREP_WIDTH: usize = width_of::<FPrepCols<u8>>();

// R2 + D17 tagged Bus 2: 142 = 126 coherence/structure + 16 (`mid` only). The
// two children blocks are terminal, so their digests ride in `parent_new`/
// `parent_old` instead of separate 16-limb output columns (−32 vs the untagged
// design), landing under the 150 soft budget.
const _: () = assert!(TABLE_F_WIDTH == 142, "Table F width");

#[derive(Clone)]
pub struct TableFAir {
    pub padded_height: usize,
    pub n_join: usize,
    pub n_open: usize,
    pub num_lookups: usize,
}

impl TableFAir {
    pub const fn new(padded_height: usize, n_join: usize, n_open: usize) -> Self {
        Self {
            padded_height,
            n_join,
            n_open,
            num_lookups: 0,
        }
    }

    fn real_rows(&self) -> usize {
        self.n_join + self.n_open
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableFAir {
    fn width(&self) -> usize {
        TABLE_F_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h * TABLE_F_PREP_WIDTH);
        for i in 0..h {
            let is_join = i < self.n_join;
            let is_open = i >= self.n_join && i < self.real_rows();
            data.push(F::from_bool(is_join));
            data.push(F::from_bool(is_open));
            data.push(F::from_bool(is_join || is_open));
        }
        Some(RowMajorMatrix::new(data, TABLE_F_PREP_WIDTH))
    }

    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for TableFAir
where
    AB::F: Send,
{
    #[allow(clippy::type_complexity)]
    fn eval(&self, builder: &mut AB) {
        let (c, p, row): (FCols<AB::Var>, FPrepCols<AB::Var>, Vec<AB::Var>) = {
            let main = builder.main();
            let prep = builder.preprocessed();
            (
                *cast(main.current_slice()),
                *cast(prep.current_slice()),
                main.current_slice().to_vec(),
            )
        };

        let one = AB::Expr::ONE;
        let e = |v: AB::Var| -> AB::Expr { v.into() };
        let is_join = e(p.is_join);
        let is_open = e(p.is_open);
        let is_real = e(p.is_real);

        // padding hygiene
        let not_real = one.clone() - is_real.clone();
        for &cell in &row {
            builder.assert_zero(not_real.clone() * e(cell));
        }

        // booleanity of flags
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

        // one-hot q on real rows; one-hot u_r/u_k on join rows
        let q_sum: AB::Expr = (0..LIMBS).map(|j| e(c.q[j])).sum();
        builder.assert_zero(q_sum - is_real.clone());
        let ur_sum: AB::Expr = (0..3).map(|i| e(c.u_r[i])).sum();
        let uk_sum: AB::Expr = (0..3).map(|i| e(c.u_k[i])).sum();
        builder.assert_zero(is_join.clone() * (ur_sum - one.clone()));
        builder.assert_zero(is_join.clone() * (uk_sum - one.clone()));

        // depth = Σ start·q + r_off (both kinds)
        let start_dot_q: AB::Expr = (0..LIMBS)
            .map(|j| e(c.q[j]) * AB::Expr::from_u32(LIMB_START[j]))
            .sum();
        builder.assert_zero(is_real.clone() * (e(c.depth) - start_dot_q - e(c.r_off)));

        // running boundary indicators for the limb one-hot
        let lt = |j: usize| -> AB::Expr { (j + 1..LIMBS).map(|k| e(c.q[k])).sum() };
        let gt = |j: usize| -> AB::Expr { (0..j).map(|k| e(c.q[k])).sum() };

        // region zero strictly above the boundary limb
        for j in 0..LIMBS {
            builder.assert_zero(gt(j) * e(c.region[j]));
        }

        // boundary-limb values selected by q
        let sel = |cols: &[AB::Var; LIMBS]| -> AB::Expr {
            (0..LIMBS).map(|j| e(c.q[j]) * e(cols[j])).sum()
        };
        let region_q = sel(&c.region);
        let l_rho_q = sel(&c.l_rho);
        let r_rho_q = sel(&c.r_rho);

        // digit reconstruction (radix 1024)
        let r1024 = |d: &[AB::Var; 3]| -> AB::Expr {
            e(d[0]) + e(d[1]) * AB::Expr::from_u32(1 << 10) + e(d[2]) * AB::Expr::from_u32(1 << 20)
        };
        builder.assert_zero(is_join.clone() * (e(c.h) - r1024(&c.h_d)));
        builder.assert_zero(e(c.has_l) * (e(c.l_l) - r1024(&c.l_l_d)));
        builder.assert_zero(e(c.has_r) * (e(c.r_l) - r1024(&c.r_l_d)));

        // r_off = 10·h_r + s_r, k = 10·h_k + s_k, with h = Σ i·u, and W = 30 − 14·q[8].
        let h_r: AB::Expr = (0..3)
            .map(|i| e(c.u_r[i]) * AB::Expr::from_u32(i as u32))
            .sum();
        let h_k: AB::Expr = (0..3)
            .map(|i| e(c.u_k[i]) * AB::Expr::from_u32(i as u32))
            .sum();
        builder
            .assert_zero(is_join.clone() * (e(c.r_off) - AB::Expr::from_u32(10) * h_r - e(c.s_r)));
        let w = AB::Expr::from_u32(30) - AB::Expr::from_u32(14) * e(c.q[8]);
        // k = W − r_off − 1
        let k = w - e(c.r_off) - one.clone();
        builder.assert_zero(is_join.clone() * (k - AB::Expr::from_u32(10) * h_k - e(c.s_k)));

        // high digits zero (above the boundary digit), gated by the one-hot.
        let gt_r = |i: usize| -> AB::Expr { (0..i).map(|j| e(c.u_r[j])).sum() };
        let gt_k = |i: usize| -> AB::Expr { (0..i).map(|j| e(c.u_k[j])).sum() };
        for i in 1..3 {
            builder.assert_zero(e(c.h_d[i]) * gt_r(i));
            builder.assert_zero(e(c.has_l) * e(c.l_l_d[i]) * gt_k(i));
            builder.assert_zero(e(c.has_r) * e(c.r_l_d[i]) * gt_k(i));
        }

        // Materialize digit widths (degree-2 local rule) so the range-bus tuple
        // element stays degree 1: width_x[i] = 10·[i<h_x] + s_x·u_x[i].
        let lt_ru = |i: usize| -> AB::Expr { (i + 1..3).map(|j| e(c.u_r[j])).sum() };
        let lt_ku = |i: usize| -> AB::Expr { (i + 1..3).map(|j| e(c.u_k[j])).sum() };
        for i in 0..3 {
            let wr = AB::Expr::from_u32(10) * lt_ru(i) + e(c.s_r) * e(c.u_r[i]);
            let wk = AB::Expr::from_u32(10) * lt_ku(i) + e(c.s_k) * e(c.u_k[i]);
            builder.assert_zero(is_join.clone() * (e(c.width_r[i]) - wr));
            builder.assert_zero(is_join.clone() * (e(c.width_k[i]) - wk));
        }

        // ==== case-bit algebra ====
        let l_none = e(c.l_none);
        let r_none = e(c.r_none);
        builder.assert_zero(is_join.clone() * (e(c.parent_none) - l_none.clone() * r_none.clone()));
        builder.assert_zero(
            is_join.clone()
                * (e(c.b11) - (one.clone() - l_none.clone()) * (one.clone() - r_none.clone())),
        );
        builder.assert_zero(
            is_join.clone() * (e(c.b01) - l_none.clone() * (one.clone() - r_none.clone())),
        );
        builder.assert_zero(is_join.clone() * (e(c.b10) - (one.clone() - l_none) * r_none));

        // four-way old-state (b00/b01/b10; b11 hash + digests on Bus 1/2 in M4)
        for j in 0..DW {
            builder.assert_zero(e(c.parent_none) * e(c.parent_old[j]));
            builder.assert_zero(e(c.b01) * (e(c.parent_old[j]) - e(c.r_old[j])));
            builder.assert_zero(e(c.b10) * (e(c.parent_old[j]) - e(c.l_old[j])));
        }

        // scalar rules
        builder
            .assert_zero(is_join.clone() * (one.clone() - e(c.has_l)) * (one.clone() - e(c.has_r)));
        builder.assert_zero(
            is_join.clone()
                * (one.clone() - e(c.b11))
                * (AB::Expr::from_u32(2) - e(c.has_l) - e(c.has_r)),
        );

        // D19: the right child sits at `parent_row_idx − 1` and the left child
        // at `rs − 1` — both are Bus-1 receive keys (below), so post-order
        // locality is enforced by the tree bus, not a local column. An opening
        // is a stream leaf: its own start equals its row index, which it hands
        // to Bus 3 through `ls` (matched against A's `subtree_start = row_idx`).
        builder.assert_zero(is_open.clone() * (e(c.ls) - e(c.parent_row_idx)));

        // ==== R10 boundary equations ====
        // pow_a = 2·pow_b; p[q] = 2·pow_b·H
        let two_pb_h = AB::Expr::from_u32(2) * e(c.pow_b) * e(c.h);
        builder.assert_zero(is_join.clone() * (region_q - two_pb_h.clone()));
        // ρ_l[q] = p[q] + L_l  (β_l = 0)
        builder.assert_zero(e(c.has_l) * (l_rho_q - two_pb_h.clone() - e(c.l_l)));
        // ρ_r[q] = p[q] + pow_b + L_r  (β_r = 1)
        builder.assert_zero(e(c.has_r) * (r_rho_q - two_pb_h - e(c.pow_b) - e(c.r_l)));

        // whole-limb prefix equalities ρ_x[j] = p[j] for j < boundary
        for j in 0..LIMBS {
            builder.assert_zero(e(c.has_l) * lt(j) * (e(c.l_rho[j]) - e(c.region[j])));
            builder.assert_zero(e(c.has_r) * lt(j) * (e(c.r_rho[j]) - e(c.region[j])));
        }

        // ==== cross-kind zeroing (join-only cols zero on opening rows) ====
        let join_only = [
            c.rs,
            c.pow_b,
            c.h,
            c.s_r,
            c.s_k,
            c.l_none,
            c.has_l,
            c.l_delta,
            c.l_l,
            c.r_none,
            c.has_r,
            c.r_delta,
            c.r_l,
            c.b01,
            c.b10,
            c.b11,
            c.parent_none,
        ];
        for col in join_only {
            builder.assert_zero(is_open.clone() * e(col));
        }
        for arr in [
            &c.h_d, &c.u_r, &c.u_k, &c.l_l_d, &c.r_l_d, &c.width_r, &c.width_k,
        ] {
            for &cell in arr {
                builder.assert_zero(is_open.clone() * e(cell));
            }
        }
        for j in 0..DW {
            builder.assert_zero(is_open.clone() * e(c.l_old[j]));
            builder.assert_zero(is_open.clone() * e(c.r_old[j]));
            // opening: old = new = digest (so the Bus-3 tuple stays degree 1).
            builder.assert_zero(is_open.clone() * (e(c.parent_old[j]) - e(c.parent_new[j])));
        }
        for j in 0..LIMBS {
            builder.assert_zero(is_open.clone() * e(c.l_rho[j]));
            builder.assert_zero(is_open.clone() * e(c.r_rho[j]));
        }
    }
}

pub const BUS_PARENT_NAME: &str = "parent";
use crate::table_a::BUS_TREE_NAME;

// Column indices into FCols (must track the field order).
const CI_PARENT_IDX: usize = 0;
const CI_LS: usize = 1;
const CI_RS: usize = 2;
const CI_DEPTH: usize = 3;
const CI_REGION: usize = 4;
const CI_Q8: usize = 21;
const CI_R_OFF: usize = 22;
const CI_POW_B: usize = 23;
const CI_L_OLD: usize = 36;
const CI_L_NEW: usize = 44;
const CI_L_NONE: usize = 52;
const CI_L_RHO: usize = 55;
const CI_R_OLD: usize = 68;
const CI_R_NEW: usize = 76;
const CI_R_NONE: usize = 84;
const CI_R_RHO: usize = 87;
const CI_B11: usize = 102;
const CI_PARENT_NONE: usize = 103;
const CI_PARENT_OLD: usize = 104;
const CI_PARENT_NEW: usize = 112;
const CI_MID: usize = 126;
use crate::table_b::{BUS_P2FF_NAME, BUS_P2TERM_NAME};
const CI_H_D: usize = 25;
const CI_HAS_L: usize = 53;
const CI_L_DELTA: usize = 54;
const CI_L_L_D: usize = 65;
const CI_HAS_R: usize = 85;
const CI_R_DELTA: usize = 86;
const CI_R_L_D: usize = 97;
const CI_WIDTH_R: usize = 120;
const CI_WIDTH_K: usize = 123;

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableFAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        use p3_air::AirLayout;
        use p3_air::symbolic::{BaseLeaf, SymbolicAirBuilder, SymbolicExpression};
        use p3_lookup::{Direction, Kind};

        use crate::table_r::BUS_RANGE_NAME;

        type SE<F> = SymbolicExpression<F>;
        self.num_lookups = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: TABLE_F_WIDTH,
            preprocessed_width: TABLE_F_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();

        let konst = |v: u32| SE::<F>::Leaf(BaseLeaf::Constant(F::from_u32(v)));
        let var = |i: usize| -> SE<F> { ml[i].into() };
        let is_join: SE<F> = pl[0].into();
        let is_real: SE<F> = pl[2].into();

        let mut lookups = Vec::new();
        let mut recv =
            |this: &mut Self, name: &str, tuple: Vec<SE<F>>, mult: SE<F>, dir: Direction| {
                lookups.push(p3_lookup::LookupAir::register_lookup(
                    this,
                    Kind::Global(name.to_string()),
                    &[(tuple, mult, dir)],
                ));
            };

        let rx = Direction::Receive;
        // Range bus (Table R): depth on every real row; per join the 3 H digits;
        // per advised child the 3 L digits + the gap byte.
        recv(
            self,
            BUS_RANGE_NAME,
            vec![konst(8), var(CI_DEPTH)],
            is_real.clone(),
            rx,
        );
        for i in 0..3 {
            recv(
                self,
                BUS_RANGE_NAME,
                vec![var(CI_WIDTH_R + i), var(CI_H_D + i)],
                is_join.clone(),
                rx,
            );
        }
        for i in 0..3 {
            recv(
                self,
                BUS_RANGE_NAME,
                vec![var(CI_WIDTH_K + i), var(CI_L_L_D + i)],
                var(CI_HAS_L),
                rx,
            );
        }
        recv(
            self,
            BUS_RANGE_NAME,
            vec![konst(8), var(CI_L_DELTA) - var(CI_DEPTH) - konst(1)],
            var(CI_HAS_L),
            rx,
        );
        for i in 0..3 {
            recv(
                self,
                BUS_RANGE_NAME,
                vec![var(CI_WIDTH_K + i), var(CI_R_L_D + i)],
                var(CI_HAS_R),
                rx,
            );
        }
        recv(
            self,
            BUS_RANGE_NAME,
            vec![konst(8), var(CI_R_DELTA) - var(CI_DEPTH) - konst(1)],
            var(CI_HAS_R),
            rx,
        );

        // Bus 7 (pow2): one pow_b receive per join, exponent k = W − r_off − 1.
        let ek = konst(30) - konst(14) * var(CI_Q8) - var(CI_R_OFF) - konst(1);
        recv(
            self,
            BUS_POW2_NAME,
            vec![ek, var(CI_POW_B)],
            is_join.clone(),
            rx,
        );

        // Bus 3 (parent): send (parent_row_idx, old[8], new[8], old_is_none,
        // depth, region[9], nhon) on every real row → A's N/O rows.
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
        ptuple.push(var(CI_B11));
        ptuple.push(var(CI_LS)); // subtree_start (D19): join parent = left start;
        // opening leaf = its own row_idx (constrained above).
        recv(
            self,
            BUS_PARENT_NAME,
            ptuple,
            is_real.clone(),
            Direction::Send,
        );

        // Bus 1 (tree): receive the two children on each join row → matches A's
        // per-row send (row_idx, subtree_start, old[8], new[8], none, has, delta,
        // rho[9]). D19: right child key = parent−1, left child key = rs−1.
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
            is_join.clone(),
            rx,
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
            is_join.clone(),
            rx,
        );

        // Bus 2 split (D17). Prefix block is feed-forward → the full
        // (input[16], mid[16]) on the feed-forward bus; `mid` feeds the children.
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
        recv(self, BUS_P2FF_NAME, pre_in, is_real.clone(), rx);
        // Children blocks are terminal → digest only (input[16], digest[0..8]) on
        // the terminal bus. The digest slot is `parent_new`/`parent_old`, so the
        // receive binds the propagated node digest to the real Poseidon2 output.
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
            is_real,
            rx,
        );
        recv(
            self,
            BUS_P2TERM_NAME,
            children(CI_L_OLD, CI_R_OLD, CI_PARENT_OLD),
            var(CI_B11),
            rx,
        );
        lookups
    }
}

// -- trace generation -------------------------------------------------------

fn push_digest(data: &mut Vec<BabyBear>, d: &[BabyBear; DW]) {
    data.extend_from_slice(d);
}
fn push_limbs(data: &mut Vec<BabyBear>, l: &Key) {
    for v in l {
        data.push(BabyBear::from_u32(*v));
    }
}
fn push_u32s(data: &mut Vec<BabyBear>, xs: &[u32]) {
    for &x in xs {
        data.push(BabyBear::from_u32(x));
    }
}
fn onehot9(data: &mut Vec<BabyBear>, idx: usize) {
    for j in 0..LIMBS {
        data.push(BabyBear::from_bool(j == idx));
    }
}
fn push_bools(data: &mut Vec<BabyBear>, bs: &[bool]) {
    for &b in bs {
        data.push(BabyBear::from_bool(b));
    }
}

fn push_join(data: &mut Vec<BabyBear>, j: &FJoin) {
    data.push(BabyBear::from_u32(j.parent_row_idx));
    data.push(BabyBear::from_u32(j.ls)); // subtree_start of left child (= parent's)
    data.push(BabyBear::from_u32(j.rs)); // subtree_start of right child
    data.push(BabyBear::from_u32(j.depth as u32));
    push_limbs(data, &j.region);
    onehot9(data, j.q);
    data.push(BabyBear::from_u32(j.r_off as u32));
    data.push(BabyBear::from_u32(j.pow_b));
    data.push(BabyBear::from_u32(j.h));
    push_u32s(data, &j.h_digits);
    push_bools(data, &j.u_r);
    data.push(BabyBear::from_u32(j.s_r as u32));
    push_bools(data, &j.u_k);
    data.push(BabyBear::from_u32(j.s_k as u32));
    // left child
    push_digest(data, &j.l_old);
    push_digest(data, &j.l_new);
    data.push(BabyBear::from_bool(j.l_none));
    data.push(BabyBear::from_bool(j.child_l.has));
    data.push(BabyBear::from_u32(j.child_l.delta as u32));
    push_limbs(data, &j.child_l.rho);
    data.push(BabyBear::from_u32(j.child_l.l));
    push_u32s(data, &j.child_l.l_digits);
    // right child
    push_digest(data, &j.r_old);
    push_digest(data, &j.r_new);
    data.push(BabyBear::from_bool(j.r_none));
    data.push(BabyBear::from_bool(j.child_r.has));
    data.push(BabyBear::from_u32(j.child_r.delta as u32));
    push_limbs(data, &j.child_r.rho);
    data.push(BabyBear::from_u32(j.child_r.l));
    push_u32s(data, &j.child_r.l_digits);
    // case bits
    let b00 = j.l_none && j.r_none;
    let b01 = j.l_none && !j.r_none;
    let b10 = !j.l_none && j.r_none;
    data.push(BabyBear::from_bool(b01));
    data.push(BabyBear::from_bool(b10));
    data.push(BabyBear::from_bool(j.b11));
    data.push(BabyBear::from_bool(b00));
    // parent tuple
    push_digest(data, &j.old_digest.unwrap_or([BabyBear::ZERO; DW]));
    push_digest(data, &j.new_digest);
    // materialized digit widths
    let h_r = j.u_r.iter().position(|&b| b).unwrap_or(0);
    let h_k = j.u_k.iter().position(|&b| b).unwrap_or(0);
    let width = |h: usize, s: u16, i: usize| -> u32 {
        use std::cmp::Ordering::*;
        match i.cmp(&h) {
            Less => 10,
            Equal => s as u32,
            Greater => 0,
        }
    };
    push_u32s(
        data,
        &[
            width(h_r, j.s_r, 0),
            width(h_r, j.s_r, 1),
            width(h_r, j.s_r, 2),
        ],
    );
    push_u32s(
        data,
        &[
            width(h_k, j.s_k, 0),
            width(h_k, j.s_k, 1),
            width(h_k, j.s_k, 2),
        ],
    );
    // shared node-sponge prefix output (feed-forward) for Bus 2
    data.extend_from_slice(&j.mid);
}

fn push_open(data: &mut Vec<BabyBear>, o: &FOpen) {
    let d = o.depth;
    let (q_idx, r_off) = if d < 240 {
        ((d / 30) as usize, d % 30)
    } else {
        (8, d - 240)
    };
    data.push(BabyBear::from_u32(o.parent_row_idx));
    data.push(BabyBear::from_u32(o.parent_row_idx)); // ls = own start (D19)
    data.push(BabyBear::ZERO); // rs (join-only, zero on opening)
    data.push(BabyBear::from_u32(d as u32));
    push_limbs(data, &o.region);
    onehot9(data, q_idx);
    data.push(BabyBear::from_u32(r_off as u32));
    // shared coherence (join-only, zero on open): pow_b, h, h_d[3], u_r[3], s_r, u_k[3], s_k
    for _ in 0..(1 + 1 + 3 + 3 + 1 + 3 + 1) {
        data.push(BabyBear::ZERO);
    }
    // left child slot: l_old zero, l_new = c_l, advice+coherence zero
    push_digest(data, &[BabyBear::ZERO; DW]);
    push_digest(data, &o.c_l);
    for _ in 0..(1 + 1 + 1 + LIMBS + 1 + 3) {
        data.push(BabyBear::ZERO);
    }
    // right child slot
    push_digest(data, &[BabyBear::ZERO; DW]);
    push_digest(data, &o.c_r);
    for _ in 0..(1 + 1 + 1 + LIMBS + 1 + 3) {
        data.push(BabyBear::ZERO);
    }
    // case bits zero
    for _ in 0..4 {
        data.push(BabyBear::ZERO);
    }
    // parent tuple: opening has old = new = digest
    push_digest(data, &o.digest);
    push_digest(data, &o.digest);
    // width columns (join-only)
    for _ in 0..6 {
        data.push(BabyBear::ZERO);
    }
    // shared node-sponge prefix output (feed-forward) for Bus 2; the opening's
    // single children block is terminal, its digest carried in the parent tuple.
    data.extend_from_slice(&o.mid);
}

/// Build Table F's main trace: all join rows then all opening rows, padded.
pub fn build_trace(plan: &TracePlan) -> (RowMajorMatrix<BabyBear>, usize, usize, usize) {
    let n_join = plan.f_joins.len();
    let n_open = plan.f_opens.len();
    let real = n_join + n_open;
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_F_WIDTH);
    for j in &plan.f_joins {
        push_join(&mut data, j);
    }
    for o in &plan.f_opens {
        push_open(&mut data, o);
    }
    for _ in real..height {
        for _ in 0..TABLE_F_WIDTH {
            data.push(BabyBear::ZERO);
        }
    }
    debug_assert_eq!(data.len(), height * TABLE_F_WIDTH);
    (
        RowMajorMatrix::new(data, TABLE_F_WIDTH),
        n_join,
        n_open,
        height,
    )
}

#[cfg(test)]
mod tests;
