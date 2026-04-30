//! Table F (N-Join) witness builder. One row per `N` opcode.
//!
//! Carries the child + parent digests and four-way old-hash selectors so the
//! AIR can express the join with purely local constraints.

use p3_field::PrimeCharacteristicRing;
use rsmt_core::{Hasher, Op};
use rsmt_hash::{DIGEST_WIDTH, Digest, State, node_hash_full};

#[derive(Clone, Debug)]
pub struct TableFRow {
    pub parent_row_idx: usize,
    pub left_ptr: usize,
    pub right_ptr: usize,
    pub depth: u8,
    pub left_old: Digest,
    pub left_new: Digest,
    pub left_none: bool,
    pub right_old: Digest,
    pub right_new: Digest,
    pub right_none: bool,
    pub parent_old: Digest,
    pub parent_new: Digest,
    pub parent_old_tail: Digest,
    pub parent_new_tail: Digest,
    pub parent_none: bool,
    pub b01: bool,
    pub b10: bool,
    pub b11: bool,
}

/// Build Table F rows from the opcode stream. Mirrors the stack simulation in
/// `build_table_a`: tracks `(Option<old>, new)` per emitted row.
pub fn build_table_f<H: Hasher<Digest = Digest>>(
    proof: &[Op<Digest>],
    sorted_batch: &[(num_bigint::BigUint, Vec<u8>)],
) -> Vec<TableFRow> {
    let mut rows = Vec::new();
    let mut row_stack: Vec<usize> = Vec::new();
    let mut digest_stack: Vec<(Option<Digest>, Digest)> = Vec::new();
    let mut bi: u32 = 0;
    let zero = [p3_baby_bear::BabyBear::ZERO; DIGEST_WIDTH];

    for (i, op) in proof.iter().enumerate() {
        match op {
            Op::S(h) => {
                let h = h.clone().expect("S(None) outside empty-batch case");
                row_stack.push(i);
                digest_stack.push((Some(h), h));
            }
            Op::L => {
                let (k, v) = &sorted_batch[bi as usize];
                let h = H::hash_leaf(k, v);
                bi += 1;
                row_stack.push(i);
                digest_stack.push((None, h));
            }
            Op::N(depth) => {
                let right_idx = row_stack.pop().expect("right child");
                let left_idx = row_stack.pop().expect("left child");
                let (rh0, rh1) = digest_stack.pop().expect("right digest");
                let (lh0, lh1) = digest_stack.pop().expect("left digest");

                let left_none = lh0.is_none();
                let right_none = rh0.is_none();
                let b01 = left_none && !right_none;
                let b10 = !left_none && right_none;
                let b11 = !left_none && !right_none;
                let parent_old_state = match (lh0, rh0) {
                    (Some(l), Some(r)) => Some(node_hash_full(&l, &r, *depth)),
                    _ => None,
                };
                let parent_old_opt = match (lh0, rh0) {
                    (None, None) => None,
                    (None, Some(r)) => Some(r),
                    (Some(l), None) => Some(l),
                    (Some(l), Some(r)) => {
                        let digest = H::hash_node(&l, &r, *depth);
                        debug_assert_eq!(
                            digest,
                            digest_from_state(parent_old_state.as_ref().expect("old state"))
                        );
                        Some(digest)
                    }
                };
                let parent_new_full = node_hash_full(&lh1, &rh1, *depth);
                let parent_new = H::hash_node(&lh1, &rh1, *depth);
                debug_assert_eq!(parent_new, digest_from_state(&parent_new_full));
                let parent_none = parent_old_opt.is_none();
                let parent_old = parent_old_opt.unwrap_or(zero);
                let parent_old_tail = parent_old_state
                    .as_ref()
                    .map(tail_from_state)
                    .unwrap_or(zero);
                let parent_new_tail = tail_from_state(&parent_new_full);

                rows.push(TableFRow {
                    parent_row_idx: i,
                    left_ptr: left_idx,
                    right_ptr: right_idx,
                    depth: *depth,
                    left_old: lh0.unwrap_or(zero),
                    left_new: lh1,
                    left_none,
                    right_old: rh0.unwrap_or(zero),
                    right_new: rh1,
                    right_none,
                    parent_old,
                    parent_new,
                    parent_old_tail,
                    parent_new_tail,
                    parent_none,
                    b01,
                    b10,
                    b11,
                });

                row_stack.push(i);
                digest_stack.push((parent_old_opt, parent_new));
            }
        }
    }
    rows
}

fn digest_from_state(state: &State) -> Digest {
    let mut digest = [p3_baby_bear::BabyBear::ZERO; DIGEST_WIDTH];
    digest.copy_from_slice(&state[..DIGEST_WIDTH]);
    digest
}

fn tail_from_state(state: &State) -> Digest {
    let mut tail = [p3_baby_bear::BabyBear::ZERO; DIGEST_WIDTH];
    tail.copy_from_slice(&state[DIGEST_WIDTH..]);
    tail
}

/// Bus 1 (`tree`) closure between Tables A and F.
///
/// Each non-root, non-padding A row sends `(row_idx, old_hash, new_hash,
/// old_is_none)`; each F row receives the same tuple twice (left + right).
/// Returns `Err((tuple_index_in_a, mismatch_kind))` on the first divergence.
pub fn check_bus_tree_closure(
    a_rows: &[crate::TableARow],
    f_rows: &[TableFRow],
) -> Result<(), String> {
    use std::collections::HashMap;
    if a_rows.is_empty() {
        return Ok(());
    }
    let mut sends: HashMap<usize, (Digest, Digest, bool)> = HashMap::new();
    let last = a_rows.len() - 1;
    for (i, r) in a_rows.iter().enumerate() {
        if i == last {
            continue;
        }
        sends.insert(r.row_idx, (r.old_hash, r.new_hash, r.old_is_none));
    }
    for f in f_rows {
        for (idx, old, new, none) in [
            (f.left_ptr, f.left_old, f.left_new, f.left_none),
            (f.right_ptr, f.right_old, f.right_new, f.right_none),
        ] {
            let s = sends
                .remove(&idx)
                .ok_or_else(|| format!("F receives missing A row {}", idx))?;
            if s.0 != old || s.1 != new || s.2 != none {
                return Err(format!("digest mismatch at row {}", idx));
            }
        }
    }
    if !sends.is_empty() {
        return Err(format!("{} A rows unconsumed", sends.len()));
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
    use crate::build_table_a;

    fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes);
        BigUint::from_bytes_be(&bytes)
    }

    #[test]
    fn bus_tree_closes_for_random_batches() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(99);
        for seed in 0..3u64 {
            let mut tree: Tree<Poseidon2Hasher> = Tree::new();
            let n = 8 + (seed as usize) * 4;
            let batch: Vec<_> = (0..n)
                .map(|_| (rand_key(&mut rng), vec![0xCDu8; 32]))
                .collect();
            let (items, proof) = tree.batch_insert(batch);
            let mut sorted = items;
            sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));
            let a = build_table_a::<Poseidon2Hasher>(&proof, &sorted);
            let f = build_table_f::<Poseidon2Hasher>(&proof, &sorted);
            check_bus_tree_closure(&a, &f).expect("bus 1 must close");
        }
    }
}
