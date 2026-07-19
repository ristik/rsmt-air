//! The empty-batch **identity transition** (R3-D11, `DEVPLAN-R3.md` §4).
//!
//! When a round applies no leaves, the transition is `old_root → old_root`. This
//! is a *separate, non-STARK* protocol case: there is no opcode stream, no batch
//! witness, and — crucially — **no zero-height AIR**. A zero-row AIR would have
//! an unconstrained boundary and could be made to "certify" an arbitrary
//! `new_root`; the identity case instead verifies by an exact field equality.
//!
//! Acceptance rule: the old root must be **present** (not the genesis `None`) and
//! equal to the new root. Genesis (`old_root_is_none = true`) is never an
//! identity — an empty genesis round produces no tree and is out of scope here.

use p3_baby_bear::BabyBear;

use crate::codec::{DIGEST_LIMBS, DecodeError};
use crate::envelope::RoundPublicInputs;

/// A verified empty-batch identity transition: `old_root = new_root`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IdentityTransition {
    pub root: [BabyBear; DIGEST_LIMBS],
}

impl IdentityTransition {
    /// Verify an identity transition against its public inputs, with **no STARK
    /// body**. Accepts only when the old root is present and equals the new root.
    pub fn verify(publics: &RoundPublicInputs) -> Result<Self, DecodeError> {
        if publics.old_root_is_none {
            // A genesis (None) old root can never be an identity: there is no
            // pre-existing state to carry forward unchanged.
            return Err(DecodeError::InvalidShape);
        }
        if publics.old_root != publics.new_root {
            return Err(DecodeError::InvalidShape);
        }
        Ok(IdentityTransition {
            root: publics.new_root,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    fn digest(seed: u32) -> [BabyBear; 8] {
        core::array::from_fn(|i| BabyBear::from_u32(seed.wrapping_add(i as u32)))
    }

    #[test]
    fn accepts_equal_present_roots() {
        let root = digest(5);
        let publics = RoundPublicInputs {
            old_root_is_none: false,
            old_root: root,
            new_root: root,
        };
        assert_eq!(
            IdentityTransition::verify(&publics),
            Ok(IdentityTransition { root })
        );
    }

    #[test]
    fn rejects_unequal_roots() {
        let publics = RoundPublicInputs {
            old_root_is_none: false,
            old_root: digest(5),
            new_root: digest(6),
        };
        assert_eq!(
            IdentityTransition::verify(&publics),
            Err(DecodeError::InvalidShape)
        );
    }

    #[test]
    fn rejects_genesis_none() {
        // Even with old_root bytes == new_root bytes, a None old root is not an
        // identity (this is exactly the "empty proof binds arbitrary roots" trap).
        let root = digest(7);
        let publics = RoundPublicInputs {
            old_root_is_none: true,
            old_root: root,
            new_root: root,
        };
        assert_eq!(
            IdentityTransition::verify(&publics),
            Err(DecodeError::InvalidShape)
        );
    }
}
