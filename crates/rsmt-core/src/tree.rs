//! Radix Sparse Merkle Tree (v6a) — Rust port of `rsmt6a.py`.
//!
//! Nodes store **absolute** `(depth, region)` (D3): splitting an edge above a
//! node changes neither, so inserting keys never re-hashes an existing node.
//! `batch_insert` mirrors `_insert / _split_edge / _build / _emit_preserved`
//! and emits the compact v6a opcode stream.

use core::marker::PhantomData;
use std::collections::BTreeMap;

use crate::hasher::Hasher;
use crate::limbs::{Key, KeyValue, first_divergence, key_bit, region_limbs};
use crate::proof::Op;

/// A tree node. Junctions carry their absolute depth and left-aligned region.
pub enum Node<H: Hasher> {
    Leaf {
        key: Key,
        value: Vec<u8>,
        hash: H::Digest,
    },
    Junction {
        depth: u16,
        region: Key,
        left: Box<Node<H>>,
        right: Box<Node<H>>,
        hash: H::Digest,
    },
}

impl<H: Hasher> Node<H> {
    pub fn hash(&self) -> &H::Digest {
        match self {
            Node::Leaf { hash, .. } | Node::Junction { hash, .. } => hash,
        }
    }

    fn new_leaf(key: Key, value: Vec<u8>) -> Box<Self> {
        let hash = H::hash_leaf(&key, &value);
        Box::new(Node::Leaf { key, value, hash })
    }

    fn new_junction(depth: u16, region: Key, left: Box<Node<H>>, right: Box<Node<H>>) -> Box<Self> {
        let hash = H::hash_node(depth, &region, left.hash(), right.hash());
        Box::new(Node::Junction {
            depth,
            region,
            left,
            right,
            hash,
        })
    }
}

/// A pre-existing leaf being merged into a freshly built subtree (leaf-merge
/// case). Emitted as `OL` when the build reaches it.
struct FrozenLeaf<D> {
    key: Key,
    value: Vec<u8>,
    hash: D,
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

    /// Descend to the leaf for `key`, if present.
    pub fn find_leaf(&self, key: &Key) -> Option<&Node<H>> {
        let mut node = self.root.as_deref()?;
        loop {
            match node {
                Node::Leaf { key: k, .. } => return if k == key { Some(node) } else { None },
                Node::Junction {
                    depth,
                    region,
                    left,
                    right,
                    ..
                } => {
                    if region_limbs(key, *depth) != *region {
                        return None;
                    }
                    node = if key_bit(key, *depth) == 1 {
                        right
                    } else {
                        left
                    };
                }
            }
        }
    }

    /// Insert new `(key, value)` pairs. Keys already present, or duplicated
    /// within `batch`, are skipped (honest dedup — an adversarial re-record is
    /// *rejected by the verifier*, not here). Returns `(applied, proof)`.
    ///
    /// An empty applied set returns `(vec![], vec![])`: the empty-batch
    /// identity transition is the caller's responsibility (D6).
    pub fn batch_insert(&mut self, batch: Vec<KeyValue>) -> (Vec<KeyValue>, Vec<Op<H::Digest>>) {
        // Keep the first occurrence of each new, not-yet-present key; BTreeMap
        // keys sort MSB-first (== integer order).
        let mut new_items: BTreeMap<Key, Vec<u8>> = BTreeMap::new();
        for (key, value) in batch {
            if new_items.contains_key(&key) || self.find_leaf(&key).is_some() {
                continue;
            }
            new_items.insert(key, value);
        }
        if new_items.is_empty() {
            return (Vec::new(), Vec::new());
        }

        let items: Vec<(Key, Vec<u8>)> = new_items.into_iter().collect();
        let mut proof = Vec::new();
        let root = std::mem::take(&mut self.root);
        let new_root = insert::<H>(root, &items, 0, items.len(), false, &mut proof);
        self.root = Some(new_root);
        (items, proof)
    }
}

/// First index in `items[lo..hi]` whose key has bit `depth` set (partition
/// point). The slice is sorted, so all set-bit keys form the suffix.
fn partition<D>(items: &[(Key, D)], lo: usize, hi: usize, depth: u16) -> usize {
    let (mut low, mut high) = (lo, hi);
    while low < high {
        let mid = (low + high) / 2;
        if key_bit(&items[mid].0, depth) == 1 {
            high = mid;
        } else {
            low = mid + 1;
        }
    }
    low
}

/// A subtree untouched this round: opaque `S` under an old junction, opened
/// one level (`O` / `OL`) under a new junction (the split edge).
fn emit_preserved<H: Hasher>(node: &Node<H>, parent_new: bool, out: &mut Vec<Op<H::Digest>>) {
    if !parent_new {
        out.push(Op::S(node.hash().clone()));
        return;
    }
    match node {
        Node::Leaf { key, value, .. } => out.push(Op::OL {
            key: *key,
            value: value.clone(),
        }),
        Node::Junction {
            depth,
            region,
            left,
            right,
            ..
        } => out.push(Op::O {
            depth: *depth,
            region: *region,
            c_l: left.hash().clone(),
            c_r: right.hash().clone(),
        }),
    }
}

/// Build a fresh subtree over sorted `items[lo..hi]`; every junction is new.
/// `frozen`, if present, is a pre-existing leaf being merged (emitted `OL`).
fn build<H: Hasher>(
    items: &[(Key, Vec<u8>)],
    lo: usize,
    hi: usize,
    frozen: Option<&FrozenLeaf<H::Digest>>,
    out: &mut Vec<Op<H::Digest>>,
) -> Box<Node<H>> {
    if hi - lo == 1 {
        let (k, v) = &items[lo];
        if let Some(f) = frozen
            && f.key == *k
        {
            out.push(Op::OL {
                key: f.key,
                value: f.value.clone(),
            });
            return Box::new(Node::Leaf {
                key: f.key,
                value: f.value.clone(),
                hash: f.hash.clone(),
            });
        }
        out.push(Op::L);
        return Node::new_leaf(*k, v.clone());
    }

    let split = first_divergence(&items[lo].0, &items[hi - 1].0);
    let region = region_limbs(&items[lo].0, split);
    let mid = partition(items, lo, hi, split);
    let ln = build::<H>(items, lo, mid, frozen, out);
    let rn = build::<H>(items, mid, hi, frozen, out);
    out.push(Op::N { depth: split });
    Node::new_junction(split, region, ln, rn)
}

fn insert<H: Hasher>(
    node: Option<Box<Node<H>>>,
    items: &[(Key, Vec<u8>)],
    lo: usize,
    hi: usize,
    parent_new: bool,
    out: &mut Vec<Op<H::Digest>>,
) -> Box<Node<H>> {
    if lo == hi {
        let node = node.expect("empty subtree without batch items");
        emit_preserved::<H>(&node, parent_new, out);
        return node;
    }

    let Some(node) = node else {
        return build::<H>(items, lo, hi, None, out);
    };

    match *node {
        Node::Leaf { key, value, hash } => {
            // Keys are pre-filtered distinct from `key`: merge and rebuild.
            let frozen = FrozenLeaf {
                key,
                value: value.clone(),
                hash,
            };
            let mut merged: Vec<(Key, Vec<u8>)> = items[lo..hi].to_vec();
            merged.push((key, value));
            merged.sort_by_key(|a| a.0);
            let len = merged.len();
            build::<H>(&merged, 0, len, Some(&frozen), out)
        }
        Node::Junction {
            depth,
            region,
            left,
            right,
            hash,
        } => {
            // Does either batch extreme diverge from this junction's region
            // above its depth?
            let mut d_div = depth;
            for probe in [&items[lo].0, &items[hi - 1].0] {
                let fd = first_divergence(probe, &region).min(depth);
                d_div = d_div.min(fd);
            }
            if d_div < depth {
                let preserved = Box::new(Node::Junction {
                    depth,
                    region,
                    left,
                    right,
                    hash,
                });
                return split_edge::<H>(preserved, region, items, lo, hi, d_div, out);
            }

            let mid = partition(items, lo, hi, depth);
            let new_left = insert::<H>(Some(left), items, lo, mid, false, out);
            let new_right = insert::<H>(Some(right), items, mid, hi, false, out);
            out.push(Op::N { depth });
            Node::new_junction(depth, region, new_left, new_right)
        }
    }
}

/// New junction at depth `d_div` above `node` (canonical edge split). The
/// preserved node keeps its absolute depth/region/hash — it is never re-hashed.
#[allow(clippy::too_many_arguments)]
fn split_edge<H: Hasher>(
    node: Box<Node<H>>,
    node_region: Key,
    items: &[(Key, Vec<u8>)],
    lo: usize,
    hi: usize,
    d_div: u16,
    out: &mut Vec<Op<H::Digest>>,
) -> Box<Node<H>> {
    let region = region_limbs(&node_region, d_div);
    let node_side = key_bit(&node_region, d_div);
    let mid = partition(items, lo, hi, d_div);
    let (ln, rn) = if node_side == 0 {
        let l = insert::<H>(Some(node), items, lo, mid, true, out);
        let r = build::<H>(items, mid, hi, None, out);
        (l, r)
    } else {
        let l = build::<H>(items, lo, mid, None, out);
        let r = insert::<H>(Some(node), items, mid, hi, true, out);
        (l, r)
    };
    out.push(Op::N { depth: d_div });
    Node::new_junction(d_div, region, ln, rn)
}
