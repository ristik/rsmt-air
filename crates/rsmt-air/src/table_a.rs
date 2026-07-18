//! Table A — proof rows (DEVPLAN M3). One row per opcode, five one-hot
//! selectors `(is_s, is_o, is_ol, is_l, is_n)`, the digest pair, the advice
//! tuple, and the opcode-specific link columns.
//!
//! Local constraints only (buses arrive in M4). Max constraint degree **2**.
//! Selector-gated rules rely on padding rows being syntactically zero (enforced
//! here), so they need no extra `is_real` factor.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_core::KEY_BITS;
use rsmt_core::LIMBS;
use rsmt_hash::DIGEST_WIDTH;
use rsmt_witness::{ARow, OpKind, Publics};

use crate::cols::{cast, width_of};

/// Main columns (37).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ACols<T> {
    // one-hot opcode selectors
    pub is_s: T,
    pub is_o: T,
    pub is_ol: T,
    pub is_l: T,
    pub is_n: T,
    // digest pair
    pub old: [T; DIGEST_WIDTH],
    pub new: [T; DIGEST_WIDTH],
    pub old_is_none: T,
    // advice tuple
    pub has_advice: T,
    pub delta: T,
    pub rho: [T; LIMBS],
    // opcode-specific links
    pub batch_idx: T,
    pub node_hash_old_needed: T,
    pub opened_idx: T,
    /// Post-order subtree start (D19). Base opcodes constrain it to `row_idx`;
    /// `N` rows receive it from Table F over Bus 3 (= left child's start). Sent
    /// on Bus 1 so a parent join can read a child's start.
    pub subtree_start: T,
}

/// Preprocessed columns (3).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct APrepCols<T> {
    pub row_idx: T,
    pub is_real: T,
    pub is_last_real: T,
}

pub const TABLE_A_WIDTH: usize = width_of::<ACols<u8>>();
pub const TABLE_A_PREP_WIDTH: usize = width_of::<APrepCols<u8>>();
/// `old_root[8]`, `new_root[8]`, and `old_root_is_none` (D20): the statement
/// distinguishes genesis `None` from `Some([0;8])`.
pub const NUM_PUBLIC: usize = 2 * DIGEST_WIDTH + 1;

const _: () = assert!(TABLE_A_WIDTH == 37);

#[derive(Clone)]
pub struct TableAAir {
    pub padded_height: usize,
    pub real_rows: usize,
    pub num_lookups: usize,
}

impl TableAAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableAAir {
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
            main_width: TABLE_A_WIDTH,
            preprocessed_width: TABLE_A_PREP_WIDTH,
            num_public_values: NUM_PUBLIC,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        // ACols: is_o(1), is_ol(2), is_l(3), is_n(4), old[5..13], new[13..21],
        // old_is_none(21), has_advice(22), delta(23), rho[24..33], batch_idx(33),
        // nhon(34), opened_idx(35), subtree_start(36).
        let is_o: SE<F> = ml[1].into();
        let is_ol: SE<F> = ml[2].into();
        let is_l: SE<F> = ml[3].into();
        let is_n: SE<F> = ml[4].into();
        let mut lookups = Vec::new();

        // Bus 4 (leaf): receive (kind=is_ol, idx=batch_idx+opened_idx, new[8], rho[9])
        // on L/OL rows.
        let idx: SE<F> = SE::<F>::from(ml[33]) + SE::<F>::from(ml[35]);
        let mut leaf: Vec<SE<F>> = vec![is_ol.clone(), idx];
        for j in 0..8 {
            leaf.push(ml[13 + j].into());
        }
        for j in 0..9 {
            leaf.push(ml[24 + j].into());
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_c::BUS_LEAF_NAME.to_string()),
            &[(leaf, is_l + is_ol.clone(), Direction::Receive)],
        ));

        // Bus 3 (parent): receive (row_idx, old[8], new[8], old_is_none, delta,
        // rho[9], nhon, subtree_start) on N/O rows → matches F's parent send.
        let mut parent: Vec<SE<F>> = vec![pl[0].into()];
        for j in 0..8 {
            parent.push(ml[5 + j].into());
        }
        for j in 0..8 {
            parent.push(ml[13 + j].into());
        }
        parent.push(ml[21].into()); // old_is_none
        parent.push(ml[23].into()); // delta (= depth)
        for j in 0..9 {
            parent.push(ml[24 + j].into()); // rho (= region)
        }
        parent.push(ml[34].into()); // nhon
        parent.push(ml[36].into()); // subtree_start (D19)
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_f::BUS_PARENT_NAME.to_string()),
            &[(parent, is_n + is_o, Direction::Receive)],
        ));

        // Bus 1 (tree): send (row_idx, subtree_start, old[8], new[8], old_is_none,
        // has_advice, delta, rho[9]) on every non-last real row → consumed by F
        // as a child. subtree_start (D19) lets the parent join derive child rows.
        let is_real: SE<F> = pl[1].into();
        let is_last: SE<F> = pl[2].into();
        let mut tree: Vec<SE<F>> = vec![pl[0].into(), ml[36].into()];
        for j in 0..8 {
            tree.push(ml[5 + j].into());
        }
        for j in 0..8 {
            tree.push(ml[13 + j].into());
        }
        tree.push(ml[21].into()); // old_is_none
        tree.push(ml[22].into()); // has_advice
        tree.push(ml[23].into()); // delta
        for j in 0..9 {
            tree.push(ml[24 + j].into()); // rho
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_TREE_NAME.to_string()),
            &[(tree, is_real - is_last, Direction::Send)],
        ));
        lookups
    }
}

pub const BUS_TREE_NAME: &str = "tree";

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableAAir {
    fn width(&self) -> usize {
        TABLE_A_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h * TABLE_A_PREP_WIDTH);
        for i in 0..h {
            data.push(F::from_u32(i as u32));
            data.push(F::from_bool(i < self.real_rows));
            data.push(F::from_bool(i + 1 == self.real_rows));
        }
        Some(RowMajorMatrix::new(data, TABLE_A_PREP_WIDTH))
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn num_public_values(&self) -> usize {
        NUM_PUBLIC
    }
}

impl<AB: AirBuilder> Air<AB> for TableAAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let prep = builder.preprocessed();
        let c: &ACols<AB::Var> = cast(main.current_slice());
        let p: &APrepCols<AB::Var> = cast(prep.current_slice());

        let one = AB::Expr::ONE;
        let e = |v: AB::Var| -> AB::Expr { v.into() };

        let is_s = e(c.is_s);
        let is_o = e(c.is_o);
        let is_ol = e(c.is_ol);
        let is_l = e(c.is_l);
        let is_n = e(c.is_n);
        let old_is_none = e(c.old_is_none);
        let has_advice = e(c.has_advice);
        let nhon = e(c.node_hash_old_needed);
        let is_real = e(p.is_real);
        let is_last = e(p.is_last_real);
        let row_idx = e(p.row_idx);

        // Booleanity of every flag.
        for b in [
            &is_s,
            &is_o,
            &is_ol,
            &is_l,
            &is_n,
            &old_is_none,
            &has_advice,
            &nhon,
        ] {
            builder.assert_zero(b.clone() * (b.clone() - one.clone()));
        }

        // One-hot: exactly one selector on a real row, none on padding.
        builder.assert_zero(
            is_s.clone() + is_o.clone() + is_ol.clone() + is_l.clone() + is_n.clone()
                - is_real.clone(),
        );

        // Advice presence: on for O/OL/L/N, off for S.
        builder.assert_zero(
            has_advice.clone() - (is_o.clone() + is_ol.clone() + is_l.clone() + is_n.clone()),
        );

        // old_is_none per opcode: S/O/OL ⇒ 0; L ⇒ 1; N free.
        builder.assert_zero((is_s.clone() + is_o.clone() + is_ol.clone()) * old_is_none.clone());
        builder.assert_zero(is_l.clone() * (one.clone() - old_is_none.clone()));

        // Digest shapes.
        let sole = is_s.clone() + is_o.clone() + is_ol.clone(); // "old = new" opcodes
        for j in 0..DIGEST_WIDTH {
            let old_j = e(c.old[j]);
            let new_j = e(c.new[j]);
            // S/O/OL ⇒ old = new
            builder.assert_zero(sole.clone() * (old_j.clone() - new_j));
            // L ⇒ old = 0
            builder.assert_zero(is_l.clone() * old_j.clone());
            // old_is_none ⇒ old = 0 (canonical zeroing)
            builder.assert_zero(old_is_none.clone() * old_j);
        }

        // Advice-tuple shapes.
        builder.assert_zero(is_s.clone() * e(c.delta)); // S ⇒ delta = 0
        // L/OL ⇒ delta = κ (256)
        let kappa = AB::Expr::from_u32(KEY_BITS as u32);
        builder.assert_zero((is_l.clone() + is_ol.clone()) * (e(c.delta) - kappa));
        for j in 0..LIMBS {
            builder.assert_zero(is_s.clone() * e(c.rho[j])); // S ⇒ rho = 0
        }

        // Link-column canonical zeroing (each free only under its opcode).
        builder.assert_zero((one.clone() - is_l.clone()) * e(c.batch_idx));
        builder.assert_zero((one.clone() - is_n.clone()) * nhon.clone());
        builder.assert_zero((one.clone() - is_o.clone() - is_ol.clone()) * e(c.opened_idx));

        // D19 post-order subtree_start. Base opcodes (S/O/OL/L) start at their own
        // row; N rows inherit the left child's start over Bus 3 (no local rule).
        let base = is_s.clone() + is_o.clone() + is_ol.clone() + is_l.clone();
        builder.assert_zero(base * (e(c.subtree_start) - row_idx));
        // The root (last real row) spans the whole trace: its start is 0.
        builder.assert_zero(is_last.clone() * e(c.subtree_start));

        // Boundary: the last real row pins the public roots and old_root_is_none.
        let pubs: Vec<AB::Expr> = builder.public_values().iter().map(|&v| v.into()).collect();
        for j in 0..DIGEST_WIDTH {
            builder.assert_zero(is_last.clone() * (e(c.old[j]) - pubs[j].clone()));
            builder.assert_zero(is_last.clone() * (e(c.new[j]) - pubs[DIGEST_WIDTH + j].clone()));
        }
        // D20: genesis `None` vs `Some([0;8])` is public.
        builder
            .assert_zero(is_last.clone() * (old_is_none.clone() - pubs[2 * DIGEST_WIDTH].clone()));

        // Padding hygiene: every main column is zero on padding rows.
        let not_real = one.clone() - is_real;
        let row = main.current_slice();
        for &cell in row {
            builder.assert_zero(not_real.clone() * e(cell));
        }
    }
}

// -- trace generation -------------------------------------------------------

fn push_digest(data: &mut Vec<BabyBear>, d: &[BabyBear; DIGEST_WIDTH]) {
    for v in d {
        data.push(*v);
    }
}

fn push_arow(data: &mut Vec<BabyBear>, r: &ARow) {
    let sel = |k: OpKind| BabyBear::from_bool(r.kind == k);
    data.push(sel(OpKind::S));
    data.push(sel(OpKind::O));
    data.push(sel(OpKind::OL));
    data.push(sel(OpKind::L));
    data.push(sel(OpKind::N));
    push_digest(data, &r.old);
    push_digest(data, &r.new);
    data.push(BabyBear::from_bool(r.old_is_none));
    data.push(BabyBear::from_bool(r.has_advice));
    data.push(BabyBear::from_u32(r.delta as u32));
    for l in r.rho {
        data.push(BabyBear::from_u32(l));
    }
    data.push(BabyBear::from_u32(r.batch_idx));
    data.push(BabyBear::from_bool(r.node_hash_old_needed));
    data.push(BabyBear::from_u32(r.opened_idx));
    data.push(BabyBear::from_u32(r.subtree_start));
}

/// Build Table A's main trace, padded to a power-of-two height (≥ 2).
pub fn build_trace(rows: &[ARow]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = rows.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_A_WIDTH);
    for r in rows {
        push_arow(&mut data, r);
    }
    for _ in real..height {
        for _ in 0..TABLE_A_WIDTH {
            data.push(BabyBear::ZERO);
        }
    }
    (RowMajorMatrix::new(data, TABLE_A_WIDTH), real, height)
}

/// The 16 public values `[old_root[8], new_root[8]]` (D6: `None` old root maps
/// to the canonical all-zero digest, carried in `Publics::old_root`).
pub fn public_values(pubs: &Publics) -> Vec<BabyBear> {
    let mut v = Vec::with_capacity(NUM_PUBLIC);
    v.extend_from_slice(&pubs.old_root);
    v.extend_from_slice(&pubs.new_root);
    v.push(BabyBear::from_bool(pubs.old_root_is_none));
    v
}

#[cfg(test)]
mod tests;
