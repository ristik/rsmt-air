//! Canonical public inputs, the transcript statement preimage, and the bounded
//! proof-envelope decoder (R3-D9, `DEVPLAN-R3.md` §6.5).
//!
//! The envelope carries **no** hash-suite, seed, or FRI selector: the only
//! protocol field is the fixed [`ProtocolId`] tag, which must equal the R3 tag
//! or decoding fails before any expensive work. The STARK proof is an opaque,
//! length-bounded blob at this layer; its opening/shape cross-check lands with
//! the verifier in M7.

use p3_baby_bear::BabyBear;

use crate::codec::{DIGEST_LIMBS, DecodeError, Reader, encode_digest};
use crate::protocol::ProtocolId;
use crate::shape::{PaddedHeights, RoundShape};

/// Hard cap on the opaque STARK blob, checked before the slice is taken
/// (allocation-limit guard). Generous relative to the ~2 MB baseline proof.
pub const MAX_STARK_BYTES: u64 = 64 * 1024 * 1024;

/// Canonical public inputs for one non-empty round. `old_root_is_none`
/// distinguishes genesis (`None`) from a present all-zero digest (D6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RoundPublicInputs {
    pub old_root_is_none: bool,
    pub old_root: [BabyBear; DIGEST_LIMBS],
    pub new_root: [BabyBear; DIGEST_LIMBS],
}

impl RoundPublicInputs {
    fn encode(&self, out: &mut Vec<u8>) {
        out.push(self.old_root_is_none as u8);
        out.extend_from_slice(&encode_digest(&self.old_root));
        out.extend_from_slice(&encode_digest(&self.new_root));
    }

    fn decode(r: &mut Reader<'_>) -> Result<Self, DecodeError> {
        let old_root_is_none = r.read_bool()?;
        let old_root = r.read_digest()?;
        let new_root = r.read_digest()?;
        Ok(RoundPublicInputs {
            old_root_is_none,
            old_root,
            new_root,
        })
    }
}

/// The one authoritative canonical statement encoding
/// (`protocol_tag ‖ publics ‖ shape`). This is exactly the preimage absorbed
/// into the Fiat–Shamir transcript before challenges (S11); changing the
/// protocol, either root, the none flag, or any shape count changes these bytes.
pub fn statement_bytes(
    protocol: ProtocolId,
    publics: &RoundPublicInputs,
    shape: &RoundShape,
) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + 1 + 64 + 56);
    out.extend_from_slice(&protocol.tag());
    publics.encode(&mut out);
    shape.encode(&mut out);
    out
}

/// A decoded proof envelope. `stark` borrows the input slice — the decoder never
/// copies the (large) proof blob.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofEnvelope<'a> {
    pub protocol: ProtocolId,
    pub publics: RoundPublicInputs,
    pub shape: RoundShape,
    pub heights: PaddedHeights,
    pub stark: &'a [u8],
}

impl<'a> ProofEnvelope<'a> {
    /// Serialize into a canonical byte envelope (test/tool helper). The verifier
    /// path only ever *decodes*.
    pub fn encode(
        protocol: ProtocolId,
        publics: &RoundPublicInputs,
        shape: &RoundShape,
        stark: &[u8],
    ) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&protocol.tag());
        publics.encode(&mut out);
        shape.encode(&mut out);
        out.extend_from_slice(&(stark.len() as u64).to_le_bytes());
        out.extend_from_slice(stark);
        out
    }

    /// Canonical, bounded decode. In order: exact protocol tag; canonical
    /// publics; shape (then full validation → padded heights, before any
    /// allocation); a length-bounded opaque STARK blob; and **no trailing
    /// bytes**. Every failure is a typed [`DecodeError`] returned before
    /// expensive work.
    pub fn decode(buf: &'a [u8]) -> Result<Self, DecodeError> {
        let mut r = Reader::new(buf);

        let mut tag = [0u8; 8];
        tag.copy_from_slice(r.read_bytes_fixed::<8>()?);
        let protocol = ProtocolId::from_tag(&tag).ok_or(DecodeError::WrongProtocol)?;

        let publics = RoundPublicInputs::decode(&mut r)?;
        let shape = RoundShape::decode(&mut r)?;
        let heights = shape.validate()?; // count identities + max height + no-wrap

        let stark = r.read_bytes(MAX_STARK_BYTES)?;
        r.finish()?; // reject trailing bytes

        Ok(ProofEnvelope {
            protocol,
            publics,
            shape,
            heights,
            stark,
        })
    }
}
