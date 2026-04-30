//! Field-agnostic Sparse Merkle Tree (RSMT3) and consistency-proof generator.
//!
//! Rust port of `ndrsmt3o.py`.

pub mod hasher;
pub mod proof;
pub mod sort_key;
pub mod tree;

pub use hasher::{Hasher, Sha256Hasher};
pub use proof::{Op, VerifyError, verify_consistency};
pub use sort_key::{KEY_BYTES, get_sort_key, key_to_bytes_be};
pub use tree::{Node, Tree};

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use rand::{RngExt, SeedableRng};
    use rand_xoshiro::Xoshiro256PlusPlus;

    use super::*;

    fn rand_key(rng: &mut Xoshiro256PlusPlus) -> BigUint {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes);
        BigUint::from_bytes_be(&bytes)
    }

    fn rand_value(rng: &mut Xoshiro256PlusPlus) -> Vec<u8> {
        let mut v = vec![0u8; 32];
        rng.fill(v.as_mut_slice());
        v
    }

    #[test]
    fn empty_batch_is_unchanged() {
        let mut tree: Tree<Sha256Hasher> = Tree::new();
        let (items, proof) = tree.batch_insert(vec![]);
        assert!(items.is_empty());
        assert_eq!(proof.len(), 1);
        assert!(matches!(proof[0], Op::S(None)));
    }

    #[test]
    fn single_leaf_roundtrip() {
        let mut tree: Tree<Sha256Hasher> = Tree::new();
        let k = BigUint::from(0x1234u64);
        let v = vec![0xAA; 4];
        let pre_root = tree.root_hash();
        let (items, proof) = tree.batch_insert(vec![(k.clone(), v.clone())]);
        let post_root = tree.root_hash().unwrap();
        verify_consistency::<Sha256Hasher>(&proof, pre_root.as_ref(), &post_root, &items)
            .expect("verify");
    }

    #[test]
    fn random_batches_verify() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(0xDEADBEEF);
        let mut tree: Tree<Sha256Hasher> = Tree::new();

        for _round in 0..6 {
            let n = 1 + (rng.random::<u32>() % 50) as usize;
            let mut batch = Vec::with_capacity(n);
            for _ in 0..n {
                batch.push((rand_key(&mut rng), rand_value(&mut rng)));
            }
            let pre_root = tree.root_hash();
            let (items, proof) = tree.batch_insert(batch);
            let post_root = tree.root_hash().unwrap();
            verify_consistency::<Sha256Hasher>(&proof, pre_root.as_ref(), &post_root, &items)
                .expect("verify");
        }
    }

    #[test]
    fn already_present_key_is_filtered() {
        let mut tree: Tree<Sha256Hasher> = Tree::new();
        let k = BigUint::from(42u64);
        let v = vec![1u8; 4];
        tree.batch_insert(vec![(k.clone(), v.clone())]);
        let pre = tree.root_hash().unwrap();

        let (items, _proof) = tree.batch_insert(vec![(k, vec![2u8; 4])]);
        assert!(items.is_empty());
        assert_eq!(tree.root_hash().unwrap(), pre);
    }

    #[test]
    fn duplicate_in_batch_is_deduped() {
        let mut tree: Tree<Sha256Hasher> = Tree::new();
        let k = BigUint::from(7u64);
        let (items, proof) = tree.batch_insert(vec![(k.clone(), vec![1]), (k.clone(), vec![2])]);
        assert_eq!(items.len(), 1);
        let post_root = tree.root_hash().unwrap();
        verify_consistency::<Sha256Hasher>(&proof, None, &post_root, &items).unwrap();
    }
}
