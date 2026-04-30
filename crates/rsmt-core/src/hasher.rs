//! Abstract hash trait for the SMT. SHA256 reference implementation matches
//! `ndrsmt3o.py`; alternative implementations (e.g. Poseidon2) plug in via
//! the same trait.

use core::fmt::Debug;

use num_bigint::BigUint;
use sha2::{Digest, Sha256};

use crate::sort_key::{KEY_BYTES, key_to_bytes_be};

pub trait Hasher: Clone {
    type Digest: Clone + Eq + Debug;

    fn hash_leaf(key: &BigUint, value: &[u8]) -> Self::Digest;
    fn hash_node(lh: &Self::Digest, rh: &Self::Digest, depth: u8) -> Self::Digest;
}

#[derive(Clone, Debug)]
pub struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    type Digest = [u8; 32];

    fn hash_leaf(key: &BigUint, value: &[u8]) -> [u8; 32] {
        let key_be = key_to_bytes_be(key);
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(key_be);
        h.update(value);
        h.finalize().into()
    }

    fn hash_node(lh: &[u8; 32], rh: &[u8; 32], depth: u8) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update([0x01, depth]);
        h.update(lh);
        h.update(rh);
        h.finalize().into()
    }
}

#[allow(dead_code)]
pub(crate) const _ASSERT_KEY_BYTES_32: () = assert!(KEY_BYTES == 32);
