//! Inclusion and non-inclusion certificates — ports of `rsmt6a.py`'s
//! `inclusion_cert / verify_inclusion` and
//! `non_inclusion_witness / verify_non_inclusion`.
//!
//! Regions never travel in a certificate: the verifier derives each expected
//! region from the queried key itself (`region_limbs(key, d)`).

use crate::hasher::Hasher;
use crate::limbs::{Key, Value32, key_bit, region_limbs};
use crate::tree::{Node, Tree};

/// Root-to-leaf inclusion certificate: junction depths and the sibling digest
/// at each. The verifier recomputes regions from the key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InclusionCert<D> {
    /// Junction depths on the path, root-to-leaf (strictly increasing).
    pub depths: Vec<u16>,
    /// Sibling digest at each junction, root-to-leaf order.
    pub siblings: Vec<D>,
}

/// One step of a non-inclusion chain along the key-directed descent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainItem<D> {
    Junction {
        depth: u16,
        region: Key,
        c_l: D,
        c_r: D,
    },
    Leaf {
        key: Key,
        value: Value32,
    },
}

impl<H: Hasher> Tree<H> {
    /// Inclusion certificate for `key`, or `None` if `key` is absent.
    pub fn inclusion_cert(&self, key: &Key) -> Option<InclusionCert<H::Digest>> {
        let mut node = self.root.as_deref()?;
        let mut depths = Vec::new();
        let mut siblings = Vec::new();
        loop {
            match node {
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
                    depths.push(*depth);
                    if key_bit(key, *depth) == 1 {
                        siblings.push(left.hash().clone());
                        node = right;
                    } else {
                        siblings.push(right.hash().clone());
                        node = left;
                    }
                }
                Node::Leaf { key: k, .. } => {
                    return if k == key {
                        Some(InclusionCert { depths, siblings })
                    } else {
                        None
                    };
                }
            }
        }
    }

    /// Non-inclusion witness for `key`: the opening chain along the
    /// key-directed descent. `Some(vec![])` for an empty tree; `None` if `key`
    /// is in fact present.
    pub fn non_inclusion_witness(&self, key: &Key) -> Option<Vec<ChainItem<H::Digest>>> {
        let Some(mut node) = self.root.as_deref() else {
            return Some(Vec::new());
        };
        let mut chain = Vec::new();
        loop {
            match node {
                Node::Leaf { key: k, value, .. } => {
                    chain.push(ChainItem::Leaf {
                        key: *k,
                        value: *value,
                    });
                    return if k != key { Some(chain) } else { None };
                }
                Node::Junction {
                    depth,
                    region,
                    left,
                    right,
                    ..
                } => {
                    chain.push(ChainItem::Junction {
                        depth: *depth,
                        region: *region,
                        c_l: left.hash().clone(),
                        c_r: right.hash().clone(),
                    });
                    if region_limbs(key, *depth) != *region {
                        return Some(chain); // divergence junction: terminal
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
}

/// Verify an inclusion certificate against `root_hash`.
pub fn verify_inclusion<H: Hasher>(
    cert: &InclusionCert<H::Digest>,
    root_hash: &H::Digest,
    key: &Key,
    value: &Value32,
) -> bool {
    if cert.depths.len() != cert.siblings.len() {
        return false;
    }
    let mut h = H::hash_leaf(key, value);
    // Deepest junction combines first (root-to-leaf stored, so iterate back).
    for i in (0..cert.depths.len()).rev() {
        let d = cert.depths[i];
        let s = &cert.siblings[i];
        let region = region_limbs(key, d);
        h = if key_bit(key, d) == 1 {
            H::hash_node(d, &region, s, &h)
        } else {
            H::hash_node(d, &region, &h, s)
        };
    }
    &h == root_hash
}

/// Verify a non-inclusion witness. `root_hash == None` denotes an empty tree,
/// for which the empty chain is the valid witness.
pub fn verify_non_inclusion<H: Hasher>(
    chain: &[ChainItem<H::Digest>],
    root_hash: Option<&H::Digest>,
    key: &Key,
) -> bool {
    let Some(root) = root_hash else {
        return chain.is_empty();
    };
    if chain.is_empty() {
        return false;
    }
    let mut expected = root.clone();
    let last = chain.len() - 1;
    for (i, item) in chain.iter().enumerate() {
        match item {
            ChainItem::Leaf { key: k, value } => {
                return i == last && H::hash_leaf(k, value) == expected && k != key;
            }
            ChainItem::Junction {
                depth,
                region,
                c_l,
                c_r,
            } => {
                if H::hash_node(*depth, region, c_l, c_r) != expected {
                    return false;
                }
                if region_limbs(key, *depth) != *region {
                    return i == last; // divergence junction: valid terminal
                }
                expected = if key_bit(key, *depth) == 1 {
                    c_r.clone()
                } else {
                    c_l.clone()
                };
            }
        }
    }
    false // chain ended without a terminal
}
