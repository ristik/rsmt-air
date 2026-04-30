//! Radix Sparse Merkle Tree v3 — Rust port of `ndrsmt3o.py`.
//!
//! Path convention (matches Python):
//! `path = (1 << len) | prefix`. A child node's start_bit equals its parent's
//! bifurcation depth, so the bit at the bifurcation depth is the *first* bit
//! of the child's prefix (constant within the subtree).

use core::marker::PhantomData;
use std::collections::BTreeMap;

use num_bigint::BigUint;

use crate::hasher::Hasher;
use crate::proof::Op;
use crate::sort_key::get_sort_key;

pub enum Node<H: Hasher> {
    Leaf {
        key: BigUint,
        value: Vec<u8>,
        hash: H::Digest,
    },
    Internal {
        path: BigUint,
        depth: u8,
        left: Box<Node<H>>,
        right: Box<Node<H>>,
        hash: H::Digest,
    },
}

impl<H: Hasher> Node<H> {
    pub fn hash(&self) -> &H::Digest {
        match self {
            Node::Leaf { hash, .. } | Node::Internal { hash, .. } => hash,
        }
    }

    fn new_leaf(key: BigUint, value: Vec<u8>) -> Self {
        let hash = H::hash_leaf(&key, &value);
        Node::Leaf { key, value, hash }
    }

    fn new_internal(path: BigUint, depth: u8, left: Box<Node<H>>, right: Box<Node<H>>) -> Self {
        let hash = H::hash_node(left.hash(), right.hash(), depth);
        Node::Internal {
            path,
            depth,
            left,
            right,
            hash,
        }
    }
}

pub struct Tree<H: Hasher> {
    pub root: Option<Box<Node<H>>>,
    _h: PhantomData<H>,
}

impl<H: Hasher> Default for Tree<H> {
    fn default() -> Self {
        Self {
            root: None,
            _h: PhantomData,
        }
    }
}

impl<H: Hasher> Tree<H> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn root_hash(&self) -> Option<H::Digest> {
        self.root.as_ref().map(|n| n.hash().clone())
    }

    pub fn find_leaf(&self, key: &BigUint) -> Option<&Node<H>> {
        let mut node = self.root.as_deref()?;
        let mut bit: u64 = 0;
        loop {
            match node {
                Node::Leaf { key: k, .. } => return if k == key { Some(node) } else { None },
                Node::Internal {
                    path, left, right, ..
                } => {
                    let n = path_len(path);
                    let prefix = low_bits(path, n);
                    if low_bits(&(key >> bit), n) != prefix {
                        return None;
                    }
                    bit += n;
                    node = if key.bit(bit) { right } else { left };
                }
            }
        }
    }

    pub fn batch_insert(
        &mut self,
        batch: Vec<(BigUint, Vec<u8>)>,
    ) -> (Vec<(BigUint, Vec<u8>)>, Vec<Op<H::Digest>>) {
        let mut new_items: BTreeMap<[u8; 32], (BigUint, Vec<u8>)> = BTreeMap::new();
        for (key, value) in batch {
            let sk = get_sort_key(&key);
            if new_items.contains_key(&sk) || self.find_leaf(&key).is_some() {
                continue;
            }
            new_items.insert(sk, (key, value));
        }

        if new_items.is_empty() {
            return (Vec::new(), vec![Op::S(self.root_hash())]);
        }

        let items: Vec<(BigUint, Vec<u8>)> = new_items.into_values().collect();
        let mut proof = Vec::new();
        let len = items.len();
        let root = std::mem::take(&mut self.root);
        let new_root = insert_proof::<H>(root, &items, 0, len, 0, &mut proof);
        self.root = Some(new_root);
        (items, proof)
    }
}

fn path_len(p: &BigUint) -> u64 {
    p.bits() - 1
}

fn low_bits(b: &BigUint, n: u64) -> BigUint {
    if n == 0 {
        return BigUint::ZERO;
    }
    let mask = (BigUint::from(1u8) << n) - BigUint::from(1u8);
    b & &mask
}

fn lowest_set_bit(b: &BigUint) -> u64 {
    b.trailing_zeros().expect("zero has no set bits")
}

fn build_subtree<H: Hasher>(
    batch: &[(BigUint, Vec<u8>)],
    start: usize,
    end: usize,
    start_bit: u64,
    proof: &mut Vec<Op<H::Digest>>,
    frozen: &Option<(BigUint, H::Digest)>,
) -> Box<Node<H>> {
    if end - start == 1 {
        let (k, v) = &batch[start];
        if let Some((fk, fh)) = frozen {
            if fk == k {
                proof.push(Op::S(Some(fh.clone())));
                return Box::new(Node::new_leaf(k.clone(), v.clone()));
            }
        }
        proof.push(Op::L);
        return Box::new(Node::new_leaf(k.clone(), v.clone()));
    }

    let xor = (&batch[start].0 ^ &batch[end - 1].0) >> start_bit;
    let split = start_bit + lowest_set_bit(&xor);

    let mut low = start;
    let mut high = end;
    while low < high {
        let mid = (low + high) / 2;
        if batch[mid].0.bit(split) {
            high = mid;
        } else {
            low = mid + 1;
        }
    }
    let mid = low;

    let n_common = split - start_bit;
    let prefix_low = low_bits(&(&batch[start].0 >> start_bit), n_common);
    let cp = (BigUint::from(1u8) << n_common) | prefix_low;

    let left = build_subtree::<H>(batch, start, mid, split, proof, frozen);
    let right = build_subtree::<H>(batch, mid, end, split, proof, frozen);
    proof.push(Op::N(split as u8));
    Box::new(Node::new_internal(cp, split as u8, left, right))
}

fn insert_proof<H: Hasher>(
    node: Option<Box<Node<H>>>,
    batch: &[(BigUint, Vec<u8>)],
    start: usize,
    end: usize,
    start_bit: u64,
    proof: &mut Vec<Op<H::Digest>>,
) -> Box<Node<H>> {
    if start == end {
        let n = node.expect("empty subtree without batch");
        proof.push(Op::S(Some(n.hash().clone())));
        return n;
    }

    let Some(n) = node else {
        return build_subtree::<H>(batch, start, end, start_bit, proof, &None);
    };

    match *n {
        Node::Leaf { key, value, hash } => {
            let frozen = Some((key.clone(), hash.clone()));
            let mut mixed: Vec<(BigUint, Vec<u8>)> = batch[start..end].to_vec();
            mixed.push((key, value));
            mixed.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));
            let len = mixed.len();
            build_subtree::<H>(&mixed, 0, len, start_bit, proof, &frozen)
        }
        Node::Internal {
            path,
            depth,
            left,
            right,
            hash: _,
        } => {
            let n_path = path_len(&path);
            let node_prefix = low_bits(&path, n_path);

            let xor_start = low_bits(&(&batch[start].0 >> start_bit), n_path) ^ &node_prefix;
            let xor_end = low_bits(&(&batch[end - 1].0 >> start_bit), n_path) ^ &node_prefix;
            let mut first_div = n_path;
            if xor_start != BigUint::ZERO {
                first_div = first_div.min(lowest_set_bit(&xor_start));
            }
            if xor_end != BigUint::ZERO {
                first_div = first_div.min(lowest_set_bit(&xor_end));
            }

            if first_div < n_path {
                return node_split_proof::<H>(
                    path, depth, left, right, batch, start, end, start_bit, first_div, proof,
                );
            }

            let split = start_bit + n_path;
            let mut low = start;
            let mut high = end;
            while low < high {
                let mid = (low + high) / 2;
                if batch[mid].0.bit(split) {
                    high = mid;
                } else {
                    low = mid + 1;
                }
            }
            let mid = low;

            let new_left = insert_proof::<H>(Some(left), batch, start, mid, split, proof);
            let new_right = insert_proof::<H>(Some(right), batch, mid, end, split, proof);
            proof.push(Op::N(depth));
            Box::new(Node::new_internal(path, depth, new_left, new_right))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn node_split_proof<H: Hasher>(
    old_path: BigUint,
    _old_depth: u8,
    left: Box<Node<H>>,
    right: Box<Node<H>>,
    batch: &[(BigUint, Vec<u8>)],
    start: usize,
    end: usize,
    start_bit: u64,
    first_div: u64,
    proof: &mut Vec<Op<H::Digest>>,
) -> Box<Node<H>> {
    let n_path = path_len(&old_path);
    let node_prefix = low_bits(&old_path, n_path);

    let n_common = first_div;
    let new_cp = (BigUint::from(1u8) << n_common) | low_bits(&node_prefix, n_common);
    let new_split = start_bit + n_common;

    // Existing node, re-rooted: shift sentinel-encoded path right by n_common.
    // First bit of new path is the bifurcation bit (constant within the subtree).
    let shifted = &old_path >> n_common;
    let new_old_path = if shifted == BigUint::ZERO {
        BigUint::from(1u8)
    } else {
        shifted
    };
    let old_depth = (start_bit + n_path) as u8;
    let shortened = Box::new(Node::new_internal(new_old_path, old_depth, left, right));

    let old_dir_bit = (&node_prefix >> n_common).bit(0);

    let mut low = start;
    let mut high = end;
    while low < high {
        let mid = (low + high) / 2;
        if batch[mid].0.bit(new_split) {
            high = mid;
        } else {
            low = mid + 1;
        }
    }
    let mid = low;

    let (new_left, new_right) = if !old_dir_bit {
        let l = insert_proof::<H>(Some(shortened), batch, start, mid, new_split, proof);
        let r = insert_proof::<H>(None, batch, mid, end, new_split, proof);
        (l, r)
    } else {
        let l = insert_proof::<H>(None, batch, start, mid, new_split, proof);
        let r = insert_proof::<H>(Some(shortened), batch, mid, end, new_split, proof);
        (l, r)
    };
    proof.push(Op::N(new_split as u8));
    Box::new(Node::new_internal(
        new_cp,
        new_split as u8,
        new_left,
        new_right,
    ))
}
