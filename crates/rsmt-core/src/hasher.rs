//! Abstract hash interface for the RSMT, plus the byte-exact SHA-256
//! reference hasher.
//!
//! The trait is parameterised over the tree's data structure (D2/D3): keys and
//! regions are 9-limb MSB-first values, node hashes carry an absolute
//! `(depth, region)`, and leaves carry `(key, value)`.
//!
//! `Sha256RefHasher` (D10) reproduces `rsmt6a.py`'s exact byte encodings so
//! Rust and Python produce **byte-identical** roots, proofs, and certificates.
//! Production hashing (`rsmt-hash::Poseidon2Hasher`) plugs into the same trait.

use core::fmt::Debug;

use sha2::{Digest as _, Sha256};

use crate::limbs::{KEY_BITS, Key, Value32, limbs_to_bytes};

/// A tree hash function. Node hashing binds the absolute `(depth, region)` of
/// the junction; leaf hashing binds `(key, value)`.
pub trait Hasher: Clone {
    type Digest: Clone + Eq + Debug;

    /// Hash a leaf. `key` is MSB-first limbs; `value` is an exact 32-byte
    /// `Value32` (no length, no truncation — R3-D1).
    fn hash_leaf(key: &Key, value: &Value32) -> Self::Digest;

    /// Hash a junction at absolute `depth` (`< 256`) with canonical
    /// left-aligned `region` limbs and child digests `lh`, `rh`.
    fn hash_node(depth: u16, region: &Key, lh: &Self::Digest, rh: &Self::Digest) -> Self::Digest;
}

/// SHA-256 reference hasher matching `rsmt6a.py`:
///
/// ```text
/// H_leaf(key, value)   = SHA256(0x00 || key_32B || value_32B)
/// H_node(d, region, l, r) = SHA256(0x01 || d_1B || region_32B || l || r)
/// ```
///
/// where `region_32B` is the left-aligned packing of the region (identical to
/// Python's `(region << (256 − d)).to_bytes(32, "big")`).
#[derive(Clone, Debug)]
pub struct Sha256RefHasher;

impl Hasher for Sha256RefHasher {
    type Digest = [u8; 32];

    fn hash_leaf(key: &Key, value: &Value32) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(limbs_to_bytes(key));
        h.update(value.as_bytes());
        h.finalize().into()
    }

    fn hash_node(depth: u16, region: &Key, lh: &[u8; 32], rh: &[u8; 32]) -> [u8; 32] {
        assert!(depth < KEY_BITS, "node depth must be < 256");
        let mut h = Sha256::new();
        h.update([0x01, depth as u8]);
        h.update(limbs_to_bytes(region));
        h.update(lh);
        h.update(rh);
        h.finalize().into()
    }
}
