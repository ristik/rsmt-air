//! Table A AIR — verification-row local constraints (no buses yet).
//!
//! Layout (24 witness columns):
//!   0: is_s   1: is_l   2: is_n
//!   3: depth  4: batch_idx
//!   5..13:  old_hash[0..8]
//!  13..21:  new_hash[0..8]
//!  21: old_is_none  22: left_ptr  23: node_hash_old_needed
//!
//! Preprocessed (3 columns):
//!   0: row_idx  1: is_real  2: is_last_real
//!
//! Public values (16):
//!   [old_root[0..8], new_root[0..8]]

use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{Air, AirBuilder, AirLayout, BaseAir, BaseLeaf, SymbolicExpression, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Direction, Kind, Lookup, LookupAir, LookupInput};
use p3_matrix::dense::RowMajorMatrix;

use rsmt_hash::DIGEST_WIDTH;
use rsmt_witness::TableARow;

pub const TABLE_A_WIDTH: usize = 24;
pub const TABLE_A_PREP_WIDTH: usize = 3;
pub const NUM_PUBLIC: usize = 2 * DIGEST_WIDTH;

const C_IS_S: usize = 0;
const C_IS_L: usize = 1;
const C_IS_N: usize = 2;
const C_DEPTH: usize = 3;
const C_BATCH_IDX: usize = 4;
const C_OLD_HASH: usize = 5;
const C_NEW_HASH: usize = 13;
const C_OLD_IS_NONE: usize = 21;
const C_LEFT_PTR: usize = 22;
const C_NHON: usize = 23;

const P_ROW_IDX: usize = 0;
const P_IS_REAL: usize = 1;
const P_IS_LAST_REAL: usize = 2;

#[derive(Clone)]
pub struct TableAAir {
    /// Length of the padded trace (must be a power of two).
    pub padded_height: usize,
    /// Number of real (non-padding) rows.
    pub real_rows: usize,
    /// Counter used during `LookupAir::add_lookup_columns`.
    pub num_lookups: usize,
}

/// Bus 1 tuple width: row_idx, old_hash[8], new_hash[8], old_is_none.
/// Depth is intentionally excluded: A rows of type S/L carry depth=0
/// while the parent's depth is recorded in F. Depth is range-checked
/// independently via Bus 5.
pub const BUS_TREE_TUPLE_WIDTH: usize = 1 + DIGEST_WIDTH + DIGEST_WIDTH + 1;
pub const BUS_TREE_NAME: &str = "tree";

/// Bus 3 tuple width: row_idx, old_hash[8], new_hash[8], old_is_none, depth,
/// node_hash_old_needed. The back-link from Table F to Table A's N rows.
pub const BUS_PARENT_TUPLE_WIDTH: usize = 1 + DIGEST_WIDTH + DIGEST_WIDTH + 1 + 1 + 1;
pub const BUS_PARENT_NAME: &str = "parent";

impl TableAAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableAAir {
    fn width(&self) -> usize {
        TABLE_A_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h * TABLE_A_PREP_WIDTH);
        for i in 0..h {
            let is_real = i < self.real_rows;
            let is_last = i + 1 == self.real_rows;
            data.push(F::from_u32(i as u32));
            data.push(F::from_bool(is_real));
            data.push(F::from_bool(is_last));
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
        let local = main.current_slice();
        let prep = builder.preprocessed().current_slice();

        let is_real = prep[P_IS_REAL];
        let is_last = prep[P_IS_LAST_REAL];
        let _row_idx = prep[P_ROW_IDX]; // currently unused locally

        let is_s = local[C_IS_S];
        let is_l = local[C_IS_L];
        let is_n = local[C_IS_N];
        let depth = local[C_DEPTH];
        let batch_idx = local[C_BATCH_IDX];
        let old_is_none = local[C_OLD_IS_NONE];
        let left_ptr = local[C_LEFT_PTR];
        let nhon = local[C_NHON];

        let one = AB::Expr::ONE;

        // Booleanity (gated by is_real).
        for &b in &[is_s, is_l, is_n, old_is_none, nhon] {
            builder.assert_zero(is_real * b * (b - one.clone()));
        }

        // One-hot opcode.
        builder.assert_zero(is_real * (is_s + is_l + is_n - one.clone()));

        // S → not none; L → none.
        builder.assert_zero(is_real * is_s * old_is_none);
        builder.assert_zero(is_real * is_l * (one.clone() - old_is_none));

        // S: old == new.
        for j in 0..DIGEST_WIDTH {
            let oh = local[C_OLD_HASH + j];
            let nh = local[C_NEW_HASH + j];
            builder.assert_zero(is_real * is_s * (oh - nh));
        }

        // L: old_hash[j] = 0.
        for j in 0..DIGEST_WIDTH {
            let oh = local[C_OLD_HASH + j];
            builder.assert_zero(is_real * is_l * oh);
        }

        // S/L canonical zero columns.
        builder.assert_zero(is_real * is_l * left_ptr);
        builder.assert_zero(is_real * is_l * depth);
        builder.assert_zero(is_real * is_l * nhon);
        builder.assert_zero(is_real * is_s * left_ptr);
        builder.assert_zero(is_real * is_s * depth);
        builder.assert_zero(is_real * is_s * batch_idx);
        builder.assert_zero(is_real * is_s * nhon);
        builder.assert_zero(is_real * is_n * batch_idx);

        // Canonical zeroing: old_is_none ⇒ old_hash zero.
        for j in 0..DIGEST_WIDTH {
            let oh = local[C_OLD_HASH + j];
            builder.assert_zero(is_real * old_is_none * oh);
        }

        // Boundary: last real row's hashes must equal the public roots.
        let pubs: Vec<AB::PublicVar> = builder.public_values().to_vec();
        for j in 0..DIGEST_WIDTH {
            let old_root = pubs[j];
            let new_root = pubs[DIGEST_WIDTH + j];
            let oh = local[C_OLD_HASH + j];
            let nh = local[C_NEW_HASH + j];
            builder.assert_zero(is_last * (oh - old_root.into()));
            builder.assert_zero(is_last * (nh - new_root.into()));
        }
        // Padding rows: every witness column must be zero (so they don't pollute
        // future LogUp multiplicities). Equivalent to is_real flipping all
        // selectors off.
        let not_real = one.clone() - is_real;
        for j in 0..TABLE_A_WIDTH {
            builder.assert_zero(not_real.clone() * local[j]);
        }
    }
}

impl<F: Field> LookupAir<F> for TableAAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.num_lookups = 0;
        let layout = AirLayout {
            main_width: TABLE_A_WIDTH,
            preprocessed_width: TABLE_A_PREP_WIDTH,
            num_public_values: NUM_PUBLIC,
            ..Default::default()
        };
        let sb = SymbolicAirBuilder::<F>::new(layout);
        let main = sb.main();
        let main_local = main.current_slice();
        let prep = sb.preprocessed();
        let prep_local = prep.current_slice();

        let one: SymbolicExpression<F> = SymbolicExpression::Leaf(BaseLeaf::Constant(F::ONE));
        let is_real: SymbolicExpression<F> = prep_local[P_IS_REAL].into();
        let is_last: SymbolicExpression<F> = prep_local[P_IS_LAST_REAL].into();
        let mult = is_real - is_last; // is_real * (1 - is_last_real), since both bool

        let mut tuple: Vec<SymbolicExpression<F>> = Vec::with_capacity(BUS_TREE_TUPLE_WIDTH);
        tuple.push(prep_local[P_ROW_IDX].into());
        for j in 0..DIGEST_WIDTH {
            tuple.push(main_local[C_OLD_HASH + j].into());
        }
        for j in 0..DIGEST_WIDTH {
            tuple.push(main_local[C_NEW_HASH + j].into());
        }
        tuple.push(main_local[C_OLD_IS_NONE].into());
        let _ = one;

        let inputs: Vec<LookupInput<F>> = vec![(tuple, mult, Direction::Send)];
        let tree_lookup =
            LookupAir::register_lookup(self, Kind::Global(BUS_TREE_NAME.to_string()), &inputs);

        // Bus 3 (parent): receive on N rows.
        let is_n: SymbolicExpression<F> = main_local[C_IS_N].into();
        let is_real_2: SymbolicExpression<F> = prep_local[P_IS_REAL].into();
        let parent_mult = is_real_2 * is_n;
        let mut parent_tuple: Vec<SymbolicExpression<F>> =
            Vec::with_capacity(BUS_PARENT_TUPLE_WIDTH);
        parent_tuple.push(prep_local[P_ROW_IDX].into());
        for j in 0..DIGEST_WIDTH {
            parent_tuple.push(main_local[C_OLD_HASH + j].into());
        }
        for j in 0..DIGEST_WIDTH {
            parent_tuple.push(main_local[C_NEW_HASH + j].into());
        }
        parent_tuple.push(main_local[C_OLD_IS_NONE].into());
        parent_tuple.push(main_local[C_DEPTH].into());
        parent_tuple.push(main_local[C_NHON].into());
        let parent_inputs: Vec<LookupInput<F>> =
            vec![(parent_tuple, parent_mult, Direction::Receive)];
        let parent_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_PARENT_NAME.to_string()),
            &parent_inputs,
        );

        // Bus 5 (u8): receive `(depth)` on N rows.
        let is_n_5: SymbolicExpression<F> = main_local[C_IS_N].into();
        let is_real_5: SymbolicExpression<F> = prep_local[P_IS_REAL].into();
        let u8_mult = is_real_5 * is_n_5;
        let u8_tuple: Vec<SymbolicExpression<F>> = vec![main_local[C_DEPTH].into()];
        let u8_inputs: Vec<LookupInput<F>> = vec![(u8_tuple, u8_mult, Direction::Receive)];
        let u8_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_e::BUS_U8_NAME.to_string()),
            &u8_inputs,
        );

        // Bus 4 (leaf_hash): receive `(batch_idx, new_hash[0..8])` on L rows.
        let is_l_4: SymbolicExpression<F> = main_local[C_IS_L].into();
        let is_real_4: SymbolicExpression<F> = prep_local[P_IS_REAL].into();
        let leaf_mult = is_real_4 * is_l_4;
        let mut leaf_tuple: Vec<SymbolicExpression<F>> = Vec::with_capacity(1 + DIGEST_WIDTH);
        leaf_tuple.push(main_local[C_BATCH_IDX].into());
        for j in 0..DIGEST_WIDTH {
            leaf_tuple.push(main_local[C_NEW_HASH + j].into());
        }
        let leaf_inputs: Vec<LookupInput<F>> = vec![(leaf_tuple, leaf_mult, Direction::Receive)];
        let leaf_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_c::BUS_LEAF_HASH_NAME.to_string()),
            &leaf_inputs,
        );

        vec![tree_lookup, parent_lookup, u8_lookup, leaf_lookup]
    }
}

/// Materialize a Table A trace (BabyBear) from witness rows. Pads to next
/// pow-2 height (≥ 2). Returns the padded matrix; the caller passes the same
/// `(real, height)` to the AIR.
pub fn build_trace_babybear(rows: &[TableARow]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = rows.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_A_WIDTH);
    for r in rows {
        push_row_bb(&mut data, r);
    }
    for _ in real..height {
        push_padding_bb(&mut data);
    }
    (RowMajorMatrix::new(data, TABLE_A_WIDTH), real, height)
}

fn push_row_bb(data: &mut Vec<BabyBear>, r: &TableARow) {
    data.push(BabyBear::from_bool(r.is_s));
    data.push(BabyBear::from_bool(r.is_l));
    data.push(BabyBear::from_bool(r.is_n));
    data.push(BabyBear::from_u32(r.depth as u32));
    data.push(BabyBear::from_u32(r.batch_idx));
    for j in 0..DIGEST_WIDTH {
        data.push(r.old_hash[j]);
    }
    for j in 0..DIGEST_WIDTH {
        data.push(r.new_hash[j]);
    }
    data.push(BabyBear::from_bool(r.old_is_none));
    data.push(BabyBear::from_u32(r.left_ptr as u32));
    data.push(BabyBear::from_bool(r.node_hash_old_needed));
}

fn push_padding_bb(data: &mut Vec<BabyBear>) {
    for _ in 0..TABLE_A_WIDTH {
        data.push(BabyBear::ZERO);
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use p3_air::check_constraints;
    use rand::{RngExt, SeedableRng};
    use rand_xoshiro::Xoshiro256PlusPlus;

    use rsmt_core::{Tree, get_sort_key};
    use rsmt_hash::Poseidon2Hasher;
    use rsmt_witness::build_table_a;

    use super::*;

    fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes);
        BigUint::from_bytes_be(&bytes)
    }

    #[test]
    fn table_a_constraints_pass_on_real_proof() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(7);
        let mut tree: Tree<Poseidon2Hasher> = Tree::new();

        let batch: Vec<_> = (0..16)
            .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
            .collect();
        let pre_root = tree.root_hash();
        let (items, proof) = tree.batch_insert(batch);
        let post_root = tree.root_hash().unwrap();
        let mut sorted = items;
        sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

        let rows = build_table_a::<Poseidon2Hasher>(&proof, &sorted);
        let (trace, real, height) = build_trace_babybear(&rows);

        let air = TableAAir::new(height, real);

        let mut publics = Vec::with_capacity(NUM_PUBLIC);
        let zero = [BabyBear::ZERO; DIGEST_WIDTH];
        let or = pre_root.unwrap_or(zero);
        for v in or {
            publics.push(v);
        }
        for v in post_root {
            publics.push(v);
        }

        check_constraints(&air, &trace, &publics);
    }
}
