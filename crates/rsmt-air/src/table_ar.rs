//! Table A (reduced, R3/M7, `DEVPLAN-R3.md` §5.2). One row per opcode with the
//! five one-hot selectors, the digest pair, `old_is_none`, the advice tuple
//! `(delta, rho[9])`, and `subtree_start`. Compared with the legacy Table A it
//! **drops** `batch_idx`, `opened_idx`, `has_advice`, and `node_hash_old_needed`:
//!
//! - leaves and openings bind to A by their **row index** (the leaf/parent bus
//!   keys), not a separate link column;
//! - `has_advice` is the derived expression `1 − is_s` (used in the tree tuple);
//! - `b11` (old node-hash needed) is derived by Table J, not round-tripped here.
//!
//! Bus tuples match Tables L/J/O: leaf `(row_idx, digest[8], key[9])`, parent
//! `(row_idx, old[8], new[8], old_none, delta, rho[9], subtree_start)` — **no
//! `nhon`** — and tree `(row_idx, subtree_start, old[8], new[8], old_none,
//! 1−is_s, delta, rho[9])`.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_core::{KEY_BITS, LIMBS};
use rsmt_hash::DIGEST_WIDTH;
use rsmt_witness::plan::OpKind;
use rsmt_witness::r3build::R3ARow;

use crate::cols::{cast, width_of};

/// Bus 1 (tree): A sends each non-last real row; J receives it as a child.
pub const BUS_TREE_NAME: &str = "tree";

/// Main columns (33).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ArCols<T> {
    pub is_s: T,
    pub is_o: T,
    pub is_ol: T,
    pub is_l: T,
    pub is_n: T,
    pub old: [T; DIGEST_WIDTH],
    pub new: [T; DIGEST_WIDTH],
    pub old_is_none: T,
    pub delta: T,
    pub rho: [T; LIMBS],
    pub subtree_start: T,
}

/// Preprocessed columns (3).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ArPrepCols<T> {
    pub row_idx: T,
    pub is_real: T,
    pub is_last_real: T,
}

pub const TABLE_AR_WIDTH: usize = width_of::<ArCols<u8>>();
pub const TABLE_AR_PREP_WIDTH: usize = width_of::<ArPrepCols<u8>>();
/// `old_root[8]`, `new_root[8]`, `old_root_is_none`.
pub const NUM_PUBLIC: usize = 2 * DIGEST_WIDTH + 1;

const _: () = assert!(TABLE_AR_WIDTH == 33);

// Column offsets into a main row.
const O_IS_S: usize = 0;
const O_OLD: usize = 5;
const O_NEW: usize = 13;
const O_OLD_NONE: usize = 21;
const O_DELTA: usize = 22;
const O_RHO: usize = 23;
const O_SST: usize = 32;

#[derive(Clone)]
pub struct TableArAir {
    pub padded_height: usize,
    pub real_rows: usize,
    pub num_lookups: usize,
}

impl TableArAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableArAir {
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
            main_width: TABLE_AR_WIDTH,
            preprocessed_width: TABLE_AR_PREP_WIDTH,
            num_public_values: NUM_PUBLIC,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        let var = |i: usize| -> SE<F> { ml[i].into() };
        let row_idx: SE<F> = pl[0].into();
        let is_real: SE<F> = pl[1].into();
        let is_last: SE<F> = pl[2].into();
        let is_s: SE<F> = var(O_IS_S);
        let is_o: SE<F> = var(O_IS_S + 1);
        let is_ol: SE<F> = var(O_IS_S + 2);
        let is_l: SE<F> = var(O_IS_S + 3);
        let is_n: SE<F> = var(O_IS_S + 4);
        let one = SE::<F>::from(F::ONE);

        let mut lookups = Vec::new();

        // leaf receive: (row_idx, digest[8]=new, key[9]=rho) on L/OL.
        let mut leaf: Vec<SE<F>> = vec![row_idx.clone()];
        for j in 0..8 {
            leaf.push(var(O_NEW + j));
        }
        for j in 0..9 {
            leaf.push(var(O_RHO + j));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_l::BUS_LEAF_NAME.to_string()),
            &[(leaf, is_l.clone() + is_ol.clone(), Direction::Receive)],
        ));

        // parent receive: (row_idx, old[8], new[8], old_none, delta, rho[9],
        // subtree_start) on N/O — matches J/O parent send (NO nhon).
        let mut parent: Vec<SE<F>> = vec![row_idx.clone()];
        for j in 0..8 {
            parent.push(var(O_OLD + j));
        }
        for j in 0..8 {
            parent.push(var(O_NEW + j));
        }
        parent.push(var(O_OLD_NONE));
        parent.push(var(O_DELTA));
        for j in 0..9 {
            parent.push(var(O_RHO + j));
        }
        parent.push(var(O_SST));
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_o::BUS_PARENT_NAME.to_string()),
            &[(parent, is_n + is_o, Direction::Receive)],
        ));

        // tree send: (row_idx, subtree_start, old[8], new[8], old_none, has=1−is_s,
        // delta, rho[9]) on non-last real rows.
        let mut tree: Vec<SE<F>> = vec![row_idx, var(O_SST)];
        for j in 0..8 {
            tree.push(var(O_OLD + j));
        }
        for j in 0..8 {
            tree.push(var(O_NEW + j));
        }
        tree.push(var(O_OLD_NONE));
        tree.push(one - is_s); // has_advice = 1 − is_s
        tree.push(var(O_DELTA));
        for j in 0..9 {
            tree.push(var(O_RHO + j));
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_ar::BUS_TREE_NAME.to_string()),
            &[(tree, is_real - is_last, Direction::Send)],
        ));
        lookups
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableArAir {
    fn width(&self) -> usize {
        TABLE_AR_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h * TABLE_AR_PREP_WIDTH);
        for i in 0..h {
            data.push(F::from_u32(i as u32));
            data.push(F::from_bool(i < self.real_rows));
            data.push(F::from_bool(i + 1 == self.real_rows));
        }
        Some(RowMajorMatrix::new(data, TABLE_AR_PREP_WIDTH))
    }

    fn num_public_values(&self) -> usize {
        NUM_PUBLIC
    }
}

impl<AB: AirBuilder> Air<AB> for TableArAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let prep = builder.preprocessed();
        let c: &ArCols<AB::Var> = cast(main.current_slice());
        let p: &ArPrepCols<AB::Var> = cast(prep.current_slice());

        let one = AB::Expr::ONE;
        let e = |v: AB::Var| -> AB::Expr { v.into() };
        let is_s = e(c.is_s);
        let is_o = e(c.is_o);
        let is_ol = e(c.is_ol);
        let is_l = e(c.is_l);
        let is_n = e(c.is_n);
        let old_is_none = e(c.old_is_none);
        let is_real = e(p.is_real);
        let is_last = e(p.is_last_real);
        let row_idx = e(p.row_idx);

        // booleanity.
        for b in [&is_s, &is_o, &is_ol, &is_l, &is_n, &old_is_none] {
            builder.assert_zero(b.clone() * (b.clone() - one.clone()));
        }
        // one-hot: exactly one selector on a real row, none on padding.
        builder.assert_zero(
            is_s.clone() + is_o.clone() + is_ol.clone() + is_l.clone() + is_n.clone()
                - is_real.clone(),
        );
        // old_is_none per opcode: S/O/OL ⇒ 0; L ⇒ 1; N free.
        builder.assert_zero((is_s.clone() + is_o.clone() + is_ol.clone()) * old_is_none.clone());
        builder.assert_zero(is_l.clone() * (one.clone() - old_is_none.clone()));

        // digest shapes.
        let sole = is_s.clone() + is_o.clone() + is_ol.clone();
        for j in 0..DIGEST_WIDTH {
            let old_j = e(c.old[j]);
            let new_j = e(c.new[j]);
            builder.assert_zero(sole.clone() * (old_j.clone() - new_j));
            builder.assert_zero(is_l.clone() * old_j.clone());
            builder.assert_zero(old_is_none.clone() * old_j);
        }

        // advice-tuple shapes.
        builder.assert_zero(is_s.clone() * e(c.delta));
        let kappa = AB::Expr::from_u32(KEY_BITS as u32);
        builder.assert_zero((is_l.clone() + is_ol.clone()) * (e(c.delta) - kappa));
        for j in 0..LIMBS {
            builder.assert_zero(is_s.clone() * e(c.rho[j]));
        }

        // subtree_start: base opcodes start at their own row; N inherits over Bus 3.
        let base = is_s.clone() + is_o + is_ol + is_l;
        builder.assert_zero(base * (e(c.subtree_start) - row_idx));
        builder.assert_zero(is_last.clone() * e(c.subtree_start));

        // boundary: the last real row pins the public roots + old_root_is_none.
        let pubs: Vec<AB::Expr> = builder.public_values().iter().map(|&v| v.into()).collect();
        for j in 0..DIGEST_WIDTH {
            builder.assert_zero(is_last.clone() * (e(c.old[j]) - pubs[j].clone()));
            builder.assert_zero(is_last.clone() * (e(c.new[j]) - pubs[DIGEST_WIDTH + j].clone()));
        }
        builder
            .assert_zero(is_last.clone() * (old_is_none.clone() - pubs[2 * DIGEST_WIDTH].clone()));

        // padding hygiene.
        let not_real = one.clone() - is_real;
        for &cell in main.current_slice() {
            builder.assert_zero(not_real.clone() * e(cell));
        }
    }
}

// -- trace generation -------------------------------------------------------

fn push_row(data: &mut Vec<BabyBear>, r: &R3ARow) {
    let sel = |k: OpKind| BabyBear::from_bool(r.kind == k);
    data.push(sel(OpKind::S));
    data.push(sel(OpKind::O));
    data.push(sel(OpKind::OL));
    data.push(sel(OpKind::L));
    data.push(sel(OpKind::N));
    data.extend_from_slice(&r.old);
    data.extend_from_slice(&r.new);
    data.push(BabyBear::from_bool(r.old_is_none));
    data.push(BabyBear::from_u32(r.delta as u32));
    for l in r.rho {
        data.push(BabyBear::from_u32(l));
    }
    data.push(BabyBear::from_u32(r.subtree_start));
}

/// Build the reduced Table A's main trace, padded to a power-of-two height.
pub fn build_trace(rows: &[R3ARow]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = rows.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_AR_WIDTH);
    for r in rows {
        push_row(&mut data, r);
    }
    for _ in real..height {
        data.extend(std::iter::repeat_n(BabyBear::ZERO, TABLE_AR_WIDTH));
    }
    (RowMajorMatrix::new(data, TABLE_AR_WIDTH), real, height)
}

/// Public values `[old_root[8], new_root[8], old_root_is_none]`.
pub fn public_values(
    old_root: &[BabyBear; 8],
    new_root: &[BabyBear; 8],
    old_none: bool,
) -> Vec<BabyBear> {
    let mut v = Vec::with_capacity(NUM_PUBLIC);
    v.extend_from_slice(old_root);
    v.extend_from_slice(new_root);
    v.push(BabyBear::from_bool(old_none));
    v
}

#[cfg(test)]
mod tests;
