//! R3/M1 canonical-domain-type golden and property tests.
//!
//! Covers the acceptance criteria of `DEVPLAN-R3.md` M1: exact-width
//! `Key32`/`Value32`, the injective byte→limb packing, the checked limb
//! constructor and `Depth`, and the `None`-old-root vs present-all-zero-digest
//! distinction. See `docs/r3/01-security-model.md` §6.

use proptest::prelude::*;
use rsmt_core::{
    Depth, KEY_BITS, Key32, Op, Sha256RefHasher, Value32, bytes_to_limbs, key_from_limbs_checked,
    limb_width, limbs_to_bytes, verify_consistency,
};

type H = Sha256RefHasher;

// -- exact-width construction: short/long rejected --------------------------

#[test]
fn value32_rejects_non_32_lengths() {
    for len in [0usize, 1, 8, 16, 31, 33, 64] {
        assert!(
            Value32::from_slice(&vec![0xABu8; len]).is_none(),
            "len {len} must be rejected"
        );
        assert!(Key32::from_slice(&vec![0xABu8; len]).is_none());
    }
    // exactly 32 accepted
    assert!(Value32::from_slice(&[0xAB; 32]).is_some());
    assert!(Key32::from_slice(&[0xAB; 32]).is_some());
}

// -- leading zero bytes are retained (no truncation/right-align aliasing) ----

#[test]
fn leading_zero_bytes_are_retained() {
    // `0x00…0001` (value = 1 in the LOW byte) must differ from `0x01 0x00…00`
    // (value = 1 in the HIGH byte). The deleted `pack_value_32` right-aligned
    // shorter inputs, so both `&[1]` and `&[0;31, 1]` would have aliased.
    let mut low = [0u8; 32];
    low[31] = 1;
    let mut high = [0u8; 32];
    high[0] = 1;
    let vlow = Value32::new(low);
    let vhigh = Value32::new(high);
    assert_ne!(vlow, vhigh);
    assert_ne!(vlow.limbs(), vhigh.limbs());
    // and neither aliases a 1-byte value: there is no way to construct one.
    assert!(Value32::from_slice(&[1u8]).is_none());
}

#[test]
fn all_zero_value_is_distinct_and_canonical() {
    let zero = Value32::new([0u8; 32]);
    assert_eq!(zero.limbs(), [0u32; 9]);
    assert_eq!(limbs_to_bytes(&zero.limbs()), [0u8; 32]);
    // distinct from a value that is zero except one bit
    let mut one = [0u8; 32];
    one[31] = 1;
    assert_ne!(zero, Value32::new(one));
}

// -- byte↔limb round trips (canonical MSB-first order, D1) -------------------

proptest! {
    #[test]
    fn key32_value32_byte_limb_roundtrip(bytes in any::<[u8; 32]>()) {
        let k = Key32::new(bytes);
        prop_assert_eq!(k.as_bytes(), &bytes);
        prop_assert_eq!(limbs_to_bytes(&k.limbs()), bytes);
        prop_assert_eq!(Key32::from_limbs(&k.limbs()), k);

        let v = Value32::new(bytes);
        prop_assert_eq!(limbs_to_bytes(&v.limbs()), bytes);
        // key and value pack identically
        prop_assert_eq!(v.limbs(), bytes_to_limbs(&bytes));
    }

    /// Injectivity: distinct 32-byte strings pack to distinct limbs.
    #[test]
    fn value32_packing_is_injective(a in any::<[u8; 32]>(), b in any::<[u8; 32]>()) {
        prop_assume!(a != b);
        prop_assert_ne!(Value32::new(a).limbs(), Value32::new(b).limbs());
    }
}

// -- checked limb constructor rejects over-wide limbs -----------------------

#[test]
fn key_from_limbs_checked_rejects_overwide() {
    // A canonical key: every limb below its width.
    let ok = bytes_to_limbs(&[0xFF; 32]);
    assert!(key_from_limbs_checked(ok).is_some());
    // Overflow each limb in turn by setting its width-th bit.
    for j in 0..9 {
        let mut bad = [0u32; 9];
        bad[j] = 1u32 << limb_width(j); // exactly 2^width — out of range
        assert!(
            key_from_limbs_checked(bad).is_none(),
            "limb {j} = 2^{} must be rejected",
            limb_width(j)
        );
    }
}

// -- checked Depth ----------------------------------------------------------

#[test]
fn depth_rejects_out_of_range() {
    assert!(Depth::new(0).is_some());
    assert_eq!(Depth::new(KEY_BITS).map(Depth::get), Some(KEY_BITS)); // leaf depth
    assert!(Depth::new(KEY_BITS + 1).is_none());
    assert!(Depth::new(u16::MAX).is_none());
}

// -- None old root vs present all-zero digest (D6) --------------------------

#[test]
fn none_old_root_distinct_from_some_zero_digest() {
    // Genesis single-leaf insertion: `L` with old side None.
    let batch = vec![(rsmt_core::key_from_u128(0xABCD), Value32::new([7u8; 32]))];
    let mut tree: rsmt_core::Tree<H> = rsmt_core::Tree::new();
    let (applied, proof) = tree.batch_insert(batch);
    let new = tree.root_hash().unwrap();
    assert_eq!(proof, vec![Op::L]);

    // Correct: old root is None (genesis).
    assert!(verify_consistency::<H>(&proof, None, &new, &applied).is_ok());
    // Substituting a *present* all-zero digest for the genesis None must fail:
    // the extracted old side is None, not Some([0;32]).
    let zero_digest = [0u8; 32];
    assert_eq!(
        verify_consistency::<H>(&proof, Some(&zero_digest), &new, &applied),
        Err(rsmt_core::VerifyError::RootMismatch)
    );
}
