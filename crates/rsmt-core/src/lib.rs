//! RSMT v6a reference core: the field-agnostic tree, the compact consistency
//! verifier, and certificate helpers. Rust port of `rsmt6a.py`.
//!
//! This crate is the **differential oracle** for the whole workspace: the
//! witness generator and AIR are validated against it. See `DEVPLAN.md` (M1).

pub mod certs;
pub mod hasher;
pub mod limbs;
pub mod proof;
pub mod tree;

pub use certs::{ChainItem, InclusionCert, verify_inclusion, verify_non_inclusion};
pub use hasher::{Hasher, Sha256RefHasher};
pub use limbs::{
    Depth, KEY_BITS, KEY_BYTES, Key, Key32, KeyValue, LIMBS, Value32, biguint_to_bytes,
    bytes_to_limbs, first_divergence, is_canonical_region, key_bit, key_from_biguint,
    key_from_limbs_checked, key_from_u128, key_to_biguint, limb_start, limb_width, limbs_to_bytes,
    region_limbs, split_limb,
};
pub use proof::{Op, VerifyError, verify_consistency};
pub use tree::{Node, Tree};

#[cfg(test)]
mod tests;
