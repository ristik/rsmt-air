//! Table F (N-Join) AIR — local constraints plus LogUp bus registrations.
//!
//! Layout (74 witness columns):
//!   0: parent_row_idx  1: left_ptr  2: right_ptr  3: depth
//!   4..12:   left_old[8]
//!  12..20:   left_new[8]
//!  20: left_none
//!  21..29:   right_old[8]
//!  29..37:   right_new[8]
//!  37: right_none
//!  38..46:   parent_old[8]
//!  46..54:   parent_new[8]
//!  54: parent_none
//!  55: b01  56: b10  57: b11
//!  58..66: parent_old_tail[8]
//!  66..74: parent_new_tail[8]
//!
//! Preprocessed (1): `is_real_f`.

use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{Air, AirBuilder, AirLayout, BaseAir, BaseLeaf, SymbolicExpression, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Direction, Kind, Lookup, LookupAir, LookupInput};
use p3_matrix::dense::RowMajorMatrix;

use crate::table_a::{BUS_PARENT_NAME, BUS_PARENT_TUPLE_WIDTH, BUS_TREE_NAME};
use crate::table_b::{BUS_POSEIDON2_NAME, BUS_POSEIDON2_TUPLE_WIDTH};

use rsmt_hash::{DIGEST_WIDTH, DOMAIN_NODE};
use rsmt_witness::TableFRow;

pub const TABLE_F_WIDTH: usize = 74;
pub const TABLE_F_PREP_WIDTH: usize = 1;

const C_PARENT_IDX: usize = 0;
const C_LEFT_PTR: usize = 1;
const C_RIGHT_PTR: usize = 2;
const C_DEPTH: usize = 3;
const C_LEFT_OLD: usize = 4;
const C_LEFT_NEW: usize = 12;
const C_LEFT_NONE: usize = 20;
const C_RIGHT_OLD: usize = 21;
const C_RIGHT_NEW: usize = 29;
const C_RIGHT_NONE: usize = 37;
const C_PARENT_OLD: usize = 38;
const C_PARENT_NEW: usize = 46;
const C_PARENT_NONE: usize = 54;
const C_B01: usize = 55;
const C_B10: usize = 56;
const C_B11: usize = 57;
const C_PARENT_OLD_TAIL: usize = 58;
const C_PARENT_NEW_TAIL: usize = 66;

#[derive(Clone)]
pub struct TableFAir {
    pub padded_height: usize,
    pub real_rows: usize,
    pub num_lookups: usize,
}

impl TableFAir {
    pub const fn new(padded_height: usize, real_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            num_lookups: 0,
        }
    }
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableFAir {
    fn width(&self) -> usize {
        TABLE_F_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h);
        for i in 0..h {
            data.push(F::from_bool(i < self.real_rows));
        }
        Some(RowMajorMatrix::new(data, TABLE_F_PREP_WIDTH))
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

impl<AB: AirBuilder> Air<AB> for TableFAir
where
    AB::F: Send,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let prep = builder.preprocessed().current_slice();

        let is_real = prep[0];
        let one = AB::Expr::ONE;

        let left_none = local[C_LEFT_NONE];
        let right_none = local[C_RIGHT_NONE];
        let parent_none = local[C_PARENT_NONE];
        let b01 = local[C_B01];
        let b10 = local[C_B10];
        let b11 = local[C_B11];

        // Booleanity.
        for &b in &[left_none, right_none, parent_none, b01, b10, b11] {
            builder.assert_zero(is_real * b * (b - one.clone()));
        }

        // right_ptr = parent_row_idx - 1.
        builder.assert_zero(is_real * (local[C_PARENT_IDX] - local[C_RIGHT_PTR] - one.clone()));

        // b01 = left_none * (1 - right_none)
        builder.assert_zero(is_real * (b01 - left_none * (one.clone() - right_none)));
        // b10 = (1 - left_none) * right_none
        builder.assert_zero(is_real * (b10 - (one.clone() - left_none) * right_none));
        // b11 = (1 - left_none) * (1 - right_none)
        builder
            .assert_zero(is_real * (b11 - (one.clone() - left_none) * (one.clone() - right_none)));
        // parent_none = left_none * right_none
        builder.assert_zero(is_real * (parent_none - left_none * right_none));

        // Four-way passthrough for old: (1 - b11) * parent_old[j]
        //                              = b01 * right_old[j] + b10 * left_old[j]
        for j in 0..DIGEST_WIDTH {
            let lo = local[C_LEFT_OLD + j];
            let ro = local[C_RIGHT_OLD + j];
            let po = local[C_PARENT_OLD + j];
            builder.assert_zero(is_real * ((one.clone() - b11) * po - (b01 * ro + b10 * lo)));
            // parent_none ⇒ parent_old[j] = 0
            builder.assert_zero(is_real * parent_none * po);
        }

        // The old-hash tail is meaningful only when the old parent is a real
        // node hash (`b11 = 1`). In passthrough/none cases it is canonical zero.
        for j in 0..DIGEST_WIDTH {
            builder.assert_zero(is_real * (one.clone() - b11) * local[C_PARENT_OLD_TAIL + j]);
        }

        // Padding rows: every witness column zero.
        let not_real = one.clone() - is_real;
        for j in 0..TABLE_F_WIDTH {
            builder.assert_zero(not_real.clone() * local[j]);
        }
    }
}

impl<F: Field> LookupAir<F> for TableFAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        self.num_lookups = 0;
        let layout = AirLayout {
            main_width: TABLE_F_WIDTH,
            preprocessed_width: TABLE_F_PREP_WIDTH,
            ..Default::default()
        };
        let sb = SymbolicAirBuilder::<F>::new(layout);
        let main = sb.main();
        let main_local = main.current_slice();
        let prep = sb.preprocessed();
        let prep_local = prep.current_slice();

        let is_real_f: SymbolicExpression<F> = prep_local[0].into();

        let mut left_tuple: Vec<SymbolicExpression<F>> = Vec::new();
        left_tuple.push(main_local[C_LEFT_PTR].into());
        for j in 0..DIGEST_WIDTH {
            left_tuple.push(main_local[C_LEFT_OLD + j].into());
        }
        for j in 0..DIGEST_WIDTH {
            left_tuple.push(main_local[C_LEFT_NEW + j].into());
        }
        left_tuple.push(main_local[C_LEFT_NONE].into());

        let mut right_tuple: Vec<SymbolicExpression<F>> = Vec::new();
        right_tuple.push(main_local[C_RIGHT_PTR].into());
        for j in 0..DIGEST_WIDTH {
            right_tuple.push(main_local[C_RIGHT_OLD + j].into());
        }
        for j in 0..DIGEST_WIDTH {
            right_tuple.push(main_local[C_RIGHT_NEW + j].into());
        }
        right_tuple.push(main_local[C_RIGHT_NONE].into());

        let left_tree_inputs: Vec<LookupInput<F>> =
            vec![(left_tuple, is_real_f.clone(), Direction::Receive)];
        let left_tree_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_TREE_NAME.to_string()),
            &left_tree_inputs,
        );
        let right_tree_inputs: Vec<LookupInput<F>> =
            vec![(right_tuple, is_real_f, Direction::Receive)];
        let right_tree_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_TREE_NAME.to_string()),
            &right_tree_inputs,
        );

        // Bus 3 (parent): send the parent tuple.
        let parent_mult: SymbolicExpression<F> = prep_local[0].into();
        let mut parent_tuple: Vec<SymbolicExpression<F>> =
            Vec::with_capacity(BUS_PARENT_TUPLE_WIDTH);
        parent_tuple.push(main_local[C_PARENT_IDX].into());
        for j in 0..DIGEST_WIDTH {
            parent_tuple.push(main_local[C_PARENT_OLD + j].into());
        }
        for j in 0..DIGEST_WIDTH {
            parent_tuple.push(main_local[C_PARENT_NEW + j].into());
        }
        parent_tuple.push(main_local[C_PARENT_NONE].into());
        parent_tuple.push(main_local[C_DEPTH].into());
        parent_tuple.push(main_local[C_B11].into());
        let parent_inputs: Vec<LookupInput<F>> = vec![(parent_tuple, parent_mult, Direction::Send)];
        let parent_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_PARENT_NAME.to_string()),
            &parent_inputs,
        );

        // Bus 2 (Poseidon2): every real F row receives the new node hash,
        // and rows with both old children (`b11`) also receive the old node hash.
        let p2_new_mult: SymbolicExpression<F> = prep_local[0].into();
        let is_real_for_p2_old: SymbolicExpression<F> = prep_local[0].into();
        let b11_for_p2_old: SymbolicExpression<F> = main_local[C_B11].into();
        let p2_old_mult = is_real_for_p2_old * b11_for_p2_old;

        let p2_new_tuple = node_hash_tuple::<F>(
            main_local,
            C_LEFT_NEW,
            C_RIGHT_NEW,
            C_PARENT_NEW,
            C_PARENT_NEW_TAIL,
        );
        let p2_old_tuple = node_hash_tuple::<F>(
            main_local,
            C_LEFT_OLD,
            C_RIGHT_OLD,
            C_PARENT_OLD,
            C_PARENT_OLD_TAIL,
        );
        debug_assert_eq!(p2_new_tuple.len(), BUS_POSEIDON2_TUPLE_WIDTH);
        debug_assert_eq!(p2_old_tuple.len(), BUS_POSEIDON2_TUPLE_WIDTH);
        let p2_new_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_POSEIDON2_NAME.to_string()),
            &[(p2_new_tuple, p2_new_mult, Direction::Receive)],
        );
        let p2_old_lookup = LookupAir::register_lookup(
            self,
            Kind::Global(BUS_POSEIDON2_NAME.to_string()),
            &[(p2_old_tuple, p2_old_mult, Direction::Receive)],
        );

        vec![
            left_tree_lookup,
            right_tree_lookup,
            parent_lookup,
            p2_new_lookup,
            p2_old_lookup,
        ]
    }
}

fn node_hash_tuple<F: Field>(
    main_local: &[p3_air::SymbolicVariable<F>],
    left_start: usize,
    right_start: usize,
    digest_start: usize,
    tail_start: usize,
) -> Vec<SymbolicExpression<F>> {
    let mut tuple = Vec::with_capacity(BUS_POSEIDON2_TUPLE_WIDTH);
    let domain_node = SymbolicExpression::Leaf(BaseLeaf::Constant(F::from_u32(DOMAIN_NODE)));
    let depth: SymbolicExpression<F> = main_local[C_DEPTH].into();

    for j in 0..DIGEST_WIDTH {
        let mut x: SymbolicExpression<F> = main_local[left_start + j].into();
        if j == 0 {
            x = x + domain_node.clone();
        } else if j == 1 {
            x = x + depth.clone();
        }
        tuple.push(x);
    }
    for j in 0..DIGEST_WIDTH {
        tuple.push(main_local[right_start + j].into());
    }
    for j in 0..DIGEST_WIDTH {
        tuple.push(main_local[digest_start + j].into());
    }
    for j in 0..DIGEST_WIDTH {
        tuple.push(main_local[tail_start + j].into());
    }
    tuple
}

pub fn build_trace_babybear(rows: &[TableFRow]) -> (RowMajorMatrix<BabyBear>, usize, usize) {
    let real = rows.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_F_WIDTH);
    for r in rows {
        push_row(&mut data, r);
    }
    for _ in real..height {
        for _ in 0..TABLE_F_WIDTH {
            data.push(BabyBear::ZERO);
        }
    }
    (RowMajorMatrix::new(data, TABLE_F_WIDTH), real, height)
}

fn push_row(data: &mut Vec<BabyBear>, r: &TableFRow) {
    data.push(BabyBear::from_u32(r.parent_row_idx as u32));
    data.push(BabyBear::from_u32(r.left_ptr as u32));
    data.push(BabyBear::from_u32(r.right_ptr as u32));
    data.push(BabyBear::from_u32(r.depth as u32));
    for j in 0..DIGEST_WIDTH {
        data.push(r.left_old[j]);
    }
    for j in 0..DIGEST_WIDTH {
        data.push(r.left_new[j]);
    }
    data.push(BabyBear::from_bool(r.left_none));
    for j in 0..DIGEST_WIDTH {
        data.push(r.right_old[j]);
    }
    for j in 0..DIGEST_WIDTH {
        data.push(r.right_new[j]);
    }
    data.push(BabyBear::from_bool(r.right_none));
    for j in 0..DIGEST_WIDTH {
        data.push(r.parent_old[j]);
    }
    for j in 0..DIGEST_WIDTH {
        data.push(r.parent_new[j]);
    }
    data.push(BabyBear::from_bool(r.parent_none));
    data.push(BabyBear::from_bool(r.b01));
    data.push(BabyBear::from_bool(r.b10));
    data.push(BabyBear::from_bool(r.b11));
    for j in 0..DIGEST_WIDTH {
        data.push(r.parent_old_tail[j]);
    }
    for j in 0..DIGEST_WIDTH {
        data.push(r.parent_new_tail[j]);
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
    use rsmt_witness::build_table_f;

    use super::*;

    fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes);
        BigUint::from_bytes_be(&bytes)
    }

    #[test]
    fn table_f_constraints_pass() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(11);
        let mut tree: Tree<Poseidon2Hasher> = Tree::new();
        let batch: Vec<_> = (0..16)
            .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
            .collect();
        let (items, proof) = tree.batch_insert(batch);
        let mut sorted = items;
        sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

        let rows = build_table_f::<Poseidon2Hasher>(&proof, &sorted);
        let (trace, real, height) = build_trace_babybear(&rows);
        let air = TableFAir::new(height, real);
        check_constraints(&air, &trace, &[]);
    }
}
