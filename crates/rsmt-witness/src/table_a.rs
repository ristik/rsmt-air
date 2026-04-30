//! Table A witness builder.
//!
//! Lowers the post-order opcode stream into one row per opcode plus the
//! `left_ptr` field derived from a stack simulation. We run the verifier
//! inline to fill `old_hash`, `new_hash`, `old_is_none`, and we keep a
//! parallel array of "digest pairs" indexed by row so that downstream
//! Table F can find each child's hashes by row index.

use num_bigint::BigUint;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

use rsmt_core::{Hasher, Op};
use rsmt_hash::{DIGEST_WIDTH, Digest};

/// One Table A row. `row_idx` is the position in the opcode stream;
/// preprocessed columns (`is_real`, `is_last_real`) are recovered by the
/// caller from the real-row count.
#[derive(Clone, Debug)]
pub struct TableARow {
    pub row_idx: usize,
    pub is_s: bool,
    pub is_l: bool,
    pub is_n: bool,
    pub depth: u8,
    pub batch_idx: u32,
    pub old_hash: Digest,
    pub new_hash: Digest,
    pub old_is_none: bool,
    pub left_ptr: usize,
    pub node_hash_old_needed: bool,
}

impl TableARow {
    fn padding() -> Self {
        Self {
            row_idx: 0,
            is_s: false,
            is_l: false,
            is_n: false,
            depth: 0,
            batch_idx: 0,
            old_hash: [BabyBear::ZERO; DIGEST_WIDTH],
            new_hash: [BabyBear::ZERO; DIGEST_WIDTH],
            old_is_none: false,
            left_ptr: 0,
            node_hash_old_needed: false,
        }
    }
}

/// Build Table A rows from an opcode stream and the (already sorted) batch.
///
/// Runs the stack-machine verifier inline to compute the `(old, new,
/// old_is_none)` triple per row, and a stack of row indices to compute
/// `left_ptr` for each N row.
pub fn build_table_a<H: Hasher<Digest = Digest>>(
    proof: &[Op<Digest>],
    sorted_batch: &[(BigUint, Vec<u8>)],
) -> Vec<TableARow> {
    let mut rows = Vec::with_capacity(proof.len());
    let mut row_stack: Vec<usize> = Vec::new();
    let mut digest_stack: Vec<(Option<Digest>, Digest)> = Vec::new();
    let mut bi: u32 = 0;

    for (i, op) in proof.iter().enumerate() {
        let mut row = TableARow::padding();
        row.row_idx = i;

        match op {
            Op::S(h) => {
                let h = h.clone().expect("S(None) outside empty-batch case");
                row.is_s = true;
                row.old_hash = h;
                row.new_hash = h;
                row.old_is_none = false;
                row_stack.push(i);
                digest_stack.push((Some(h), h));
            }
            Op::L => {
                let (k, v) = &sorted_batch[bi as usize];
                let h = H::hash_leaf(k, v);
                row.is_l = true;
                row.batch_idx = bi;
                row.new_hash = h;
                row.old_is_none = true;
                bi += 1;
                row_stack.push(i);
                digest_stack.push((None, h));
            }
            Op::N(depth) => {
                let right_idx = row_stack.pop().expect("right child");
                let left_idx = row_stack.pop().expect("left child");
                let (rh0, rh1) = digest_stack.pop().expect("right digest");
                let (lh0, lh1) = digest_stack.pop().expect("left digest");

                row.is_n = true;
                row.depth = *depth;
                row.left_ptr = left_idx;
                debug_assert_eq!(right_idx, i.checked_sub(1).unwrap_or(usize::MAX));

                let h0 = match (lh0, rh0) {
                    (None, None) => None,
                    (None, Some(r)) => Some(r),
                    (Some(l), None) => Some(l),
                    (Some(l), Some(r)) => Some(H::hash_node(&l, &r, *depth)),
                };
                let h1 = H::hash_node(&lh1, &rh1, *depth);
                row.old_is_none = h0.is_none();
                row.old_hash = h0.unwrap_or([BabyBear::ZERO; DIGEST_WIDTH]);
                row.new_hash = h1;
                row.node_hash_old_needed = match (lh0, rh0) {
                    (Some(_), Some(_)) => true,
                    _ => false,
                };
                row_stack.push(i);
                digest_stack.push((h0, h1));
            }
        }
        rows.push(row);
    }

    debug_assert_eq!(row_stack.len(), 1, "post-order should leave one root");
    debug_assert_eq!(digest_stack.len(), 1);
    rows
}

/// Bus 1 (`tree`) multiset balance check.
///
/// Every non-root real Table A row must appear exactly once as a child
/// (left or right) of some Table F (N-Join) row. Equivalently: for each
/// non-root row index `r`, the number of N rows with `left_ptr = r` plus
/// the number with `right_ptr (= row_idx - 1) = r` equals exactly one.
///
/// Returns `Err((row_idx, count))` on the first imbalance.
pub fn check_tree_bus_balance(rows: &[TableARow]) -> Result<(), (usize, usize)> {
    if rows.is_empty() {
        return Ok(());
    }
    let n_rows = rows.len();
    let mut child_count = vec![0usize; n_rows];
    for row in rows {
        if row.is_n {
            child_count[row.left_ptr] += 1;
            if row.row_idx > 0 {
                child_count[row.row_idx - 1] += 1;
            }
        }
    }
    let root_idx = n_rows - 1;
    for (i, c) in child_count.iter().enumerate() {
        let expected = if i == root_idx { 0 } else { 1 };
        if *c != expected {
            return Err((i, *c));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use rand::{RngExt, SeedableRng};
    use rand_xoshiro::Xoshiro256PlusPlus;

    use rsmt_core::{Tree, get_sort_key};
    use rsmt_hash::Poseidon2Hasher;

    use super::*;

    fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes);
        BigUint::from_bytes_be(&bytes)
    }

    #[test]
    fn table_a_balances_for_random_batches() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(42);
        let mut tree: Tree<Poseidon2Hasher> = Tree::new();

        for _ in 0..3 {
            let n = 8 + (rand::random::<u8>() as usize % 24);
            let batch: Vec<_> = (0..n)
                .map(|_| (rand_key(&mut rng), vec![0xABu8; 32]))
                .collect();
            let (items, proof) = tree.batch_insert(batch);
            if items.is_empty() {
                continue;
            }

            let mut sorted = items.clone();
            sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

            let rows = build_table_a::<Poseidon2Hasher>(&proof, &sorted);
            assert_eq!(rows.len(), proof.len());

            // Last row's hashes must equal the post-state root.
            let post_root = tree.root_hash().unwrap();
            assert_eq!(rows.last().unwrap().new_hash, post_root);

            check_tree_bus_balance(&rows).expect("tree bus multiset must balance");
        }
    }
}
