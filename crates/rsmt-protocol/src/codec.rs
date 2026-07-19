//! Canonical little-endian codec for BabyBear base and quartic-extension field
//! elements (R3-D9, `docs/r3/01-security-model.md` §6). Every field element has
//! exactly one accepted external encoding: a base element is a 4-byte LE integer
//! in `[0, p)`; an extension element is four canonical base coefficients.
//!
//! The decoder never allocates and rejects any integer `>= p` — there is no
//! non-canonical or overlong form.

use p3_baby_bear::BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};

/// BabyBear modulus `p = 2^31 - 2^27 + 1`.
pub const BABYBEAR_ORDER: u32 = 0x7800_0001;

/// Bytes in a canonical base-field element.
pub const BASE_BYTES: usize = 4;
/// Extension degree (`BinomialExtensionField<BabyBear, 4>`).
pub const EXT_DEGREE: usize = 4;
/// Bytes in a canonical extension-field element.
pub const EXT_BYTES: usize = BASE_BYTES * EXT_DEGREE;
/// Bytes in a digest (`[BabyBear; 8]`).
pub const DIGEST_LIMBS: usize = 8;
/// Bytes in a canonical digest.
pub const DIGEST_BYTES: usize = BASE_BYTES * DIGEST_LIMBS;

/// A canonical-decoding failure. Distinct variants so negative tests can assert
/// the exact rejection reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// A base-field integer was `>= p` (non-canonical).
    NonCanonicalFieldElement,
    /// Input ended before the expected number of bytes.
    UnexpectedEof,
    /// Bytes remained after a complete decode (no trailing data allowed).
    TrailingBytes,
    /// A boolean byte was neither `0` nor `1`.
    NonCanonicalBool,
    /// A declared length exceeded its protocol maximum (checked before alloc).
    LengthLimitExceeded,
    /// The envelope named a protocol other than the fixed R3 protocol.
    WrongProtocol,
    /// A shape count identity or bound was violated.
    InvalidShape,
}

/// Encode one base element as 4 canonical LE bytes.
pub fn encode_base(x: BabyBear) -> [u8; BASE_BYTES] {
    x.as_canonical_u32().to_le_bytes()
}

/// Decode one canonical base element, rejecting integers `>= p`.
pub fn decode_base(bytes: &[u8; BASE_BYTES]) -> Result<BabyBear, DecodeError> {
    let v = u32::from_le_bytes(*bytes);
    if v >= BABYBEAR_ORDER {
        return Err(DecodeError::NonCanonicalFieldElement);
    }
    Ok(BabyBear::from_u32(v))
}

/// Encode a digest as 8 canonical base elements (32 bytes).
pub fn encode_digest(d: &[BabyBear; DIGEST_LIMBS]) -> [u8; DIGEST_BYTES] {
    let mut out = [0u8; DIGEST_BYTES];
    for (i, limb) in d.iter().enumerate() {
        out[i * BASE_BYTES..(i + 1) * BASE_BYTES].copy_from_slice(&encode_base(*limb));
    }
    out
}

/// A forward-only reader over a byte slice with canonical, bounded reads.
pub struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Reader { buf, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
        let end = self.pos.checked_add(n).ok_or(DecodeError::UnexpectedEof)?;
        if end > self.buf.len() {
            return Err(DecodeError::UnexpectedEof);
        }
        let s = &self.buf[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    /// Borrow exactly `N` bytes (fixed-width field, e.g. the protocol tag).
    pub fn read_bytes_fixed<const N: usize>(&mut self) -> Result<&'a [u8], DecodeError> {
        self.take(N)
    }

    /// Read one canonical boolean (`0` or `1`).
    pub fn read_bool(&mut self) -> Result<bool, DecodeError> {
        match self.take(1)?[0] {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(DecodeError::NonCanonicalBool),
        }
    }

    /// Read a fixed-width unsigned integer (LE, `u64`).
    pub fn read_u64(&mut self) -> Result<u64, DecodeError> {
        let s = self.take(8)?;
        Ok(u64::from_le_bytes(s.try_into().unwrap()))
    }

    /// Read a bounded length prefix (`u64` LE) and check it against `max`
    /// *before* the caller allocates.
    pub fn read_len(&mut self, max: u64) -> Result<usize, DecodeError> {
        let n = self.read_u64()?;
        if n > max {
            return Err(DecodeError::LengthLimitExceeded);
        }
        Ok(n as usize)
    }

    /// Read one canonical base-field element.
    pub fn read_base(&mut self) -> Result<BabyBear, DecodeError> {
        let s = self.take(BASE_BYTES)?;
        decode_base(&s.try_into().unwrap())
    }

    /// Read a canonical digest (`[BabyBear; 8]`).
    pub fn read_digest(&mut self) -> Result<[BabyBear; DIGEST_LIMBS], DecodeError> {
        let mut d = [BabyBear::ZERO; DIGEST_LIMBS];
        for limb in d.iter_mut() {
            *limb = self.read_base()?;
        }
        Ok(d)
    }

    /// Borrow `n` raw bytes (e.g. an opaque STARK blob), bounded by `max`.
    pub fn read_bytes(&mut self, max: u64) -> Result<&'a [u8], DecodeError> {
        let n = self.read_len(max)?;
        self.take(n)
    }

    /// Assert the whole buffer was consumed (no trailing bytes).
    pub fn finish(self) -> Result<(), DecodeError> {
        if self.pos == self.buf.len() {
            Ok(())
        } else {
            Err(DecodeError::TrailingBytes)
        }
    }
}
