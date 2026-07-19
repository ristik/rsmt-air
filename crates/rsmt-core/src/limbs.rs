//! MSB-first 256-bit key / region encoding.
//!
//! Design decisions (see `DEVPLAN.md`):
//!
//! - **D1 — bit order.** Plain MSB-first, as in `rsmt6a.py`. Bit position `d`
//!   counts from the most-significant bit (`d = 0` is the top bit,
//!   `d = 255` is the low bit). The traversal sort key is the big-endian key
//!   bytes themselves; there is no bit reversal.
//! - **D2 — key type.** `[u8; 32]` at API edges, `[u32; 9]` limbs internally.
//!   Limbs 0..7 hold 30 bits each, limb 8 holds 16 bits, and **limb 0 is the
//!   most significant**. `BigUint` only appears in tests/CLI parsing.
//! - **D3 — region.** The same 9-limb packing applied to `region << (256 − d)`
//!   — left-aligned, zero-filled below bit `d`. A leaf's region is its key
//!   limbs verbatim. One canonical encoding per region.
//!
//! All limb values are `< 2^30 < BabyBear::ORDER`, so the same representation
//! feeds the field hashers unchanged.

use num_bigint::BigUint;

/// Bytes per 256-bit key.
pub const KEY_BYTES: usize = 32;
/// Bit width of a key; also the depth `κ` of a leaf.
pub const KEY_BITS: u16 = 256;
/// Number of BabyBear limbs a key packs into.
pub const LIMBS: usize = 9;
/// Bit width of the wide (leading) limbs 0..7.
pub const WIDE_LIMB_BITS: u16 = 30;
/// Bit width of the final limb 8.
pub const LAST_LIMB_BITS: u16 = 16;
/// Number of wide (30-bit) limbs before the 16-bit tail limb.
pub const WIDE_LIMBS: usize = 8;

/// A 256-bit key or region as 9 MSB-first BabyBear-sized limbs (D2/D3).
pub type Key = [u32; LIMBS];

/// A `(key, value)` batch/leaf pair. The value is **exactly** 32 bytes
/// (`Value32`) — there is no length field and no implicit truncation/padding
/// (R3-D1, finding §4: `pack_value_32` aliasing).
pub type KeyValue = (Key, Value32);

/// Canonical external 32-byte key (R3-D1). Byte order is big-endian / MSB-first
/// (D1): byte 0 is the most-significant key byte. [`Key32::limbs`] is the
/// injective packing into the internal 9-limb representation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Key32([u8; KEY_BYTES]);

impl Key32 {
    /// Wrap 32 bytes verbatim.
    pub const fn new(bytes: [u8; KEY_BYTES]) -> Self {
        Key32(bytes)
    }

    /// Checked exact-width conversion: `Some` iff `s.len() == 32`. Rejects both
    /// short and long inputs — no truncation, no implicit padding.
    pub fn from_slice(s: &[u8]) -> Option<Self> {
        (s.len() == KEY_BYTES).then(|| {
            let mut b = [0u8; KEY_BYTES];
            b.copy_from_slice(s);
            Key32(b)
        })
    }

    /// The 32 canonical bytes.
    pub const fn as_bytes(&self) -> &[u8; KEY_BYTES] {
        &self.0
    }

    /// Injective packing into the internal MSB-first limb representation.
    pub fn limbs(&self) -> Key {
        bytes_to_limbs(&self.0)
    }

    /// Recover the byte key from canonical limbs.
    pub fn from_limbs(limbs: &Key) -> Self {
        Key32(limbs_to_bytes(limbs))
    }
}

/// Opaque canonical 256-bit leaf value (R3-D1). The RSMT layer does not
/// interpret it; applications hash their payload to a `Value32` with their own
/// domain separation (see `docs/r3/01-security-model.md` §5). It is exactly 32
/// bytes so byte→field packing is injective and every leaf is exactly three
/// Poseidon2 permutations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Value32([u8; KEY_BYTES]);

impl Value32 {
    /// Wrap 32 bytes verbatim.
    pub const fn new(bytes: [u8; KEY_BYTES]) -> Self {
        Value32(bytes)
    }

    /// Checked exact-width conversion: `Some` iff `s.len() == 32`. This is the
    /// injective replacement for the deleted `pack_value_32(&[u8])`, which
    /// truncated after 32 bytes and right-aligned shorter values (finding §4).
    pub fn from_slice(s: &[u8]) -> Option<Self> {
        (s.len() == KEY_BYTES).then(|| {
            let mut b = [0u8; KEY_BYTES];
            b.copy_from_slice(s);
            Value32(b)
        })
    }

    /// The 32 canonical bytes.
    pub const fn as_bytes(&self) -> &[u8; KEY_BYTES] {
        &self.0
    }

    /// Injective packing into 9 MSB-first limbs (identical to key packing).
    pub fn limbs(&self) -> Key {
        bytes_to_limbs(&self.0)
    }
}

/// A checked absolute depth in `[0, 256]`. Constructing one rejects the
/// out-of-range depths the reference verifier would reject as `BadDepth`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Depth(u16);

impl Depth {
    /// `Some` iff `d <= 256` (a leaf sits at `KEY_BITS = 256`).
    pub const fn new(d: u16) -> Option<Self> {
        if d <= KEY_BITS { Some(Depth(d)) } else { None }
    }

    /// The raw depth.
    pub const fn get(self) -> u16 {
        self.0
    }
}

/// Construct a `Key` from raw limbs, rejecting any limb wider than its fixed
/// width (`30,…,30,16` bits). This is the only checked path for building limbs
/// that did not come from [`bytes_to_limbs`]; it closes the "field-limb preimage
/// that is not a byte-encoded key" gap at the reference layer.
pub fn key_from_limbs_checked(limbs: Key) -> Option<Key> {
    for (j, l) in limbs.iter().enumerate() {
        if *l >= (1u32 << limb_width(j)) {
            return None;
        }
    }
    Some(limbs)
}

const _: () = assert!(
    (WIDE_LIMBS as u16) * WIDE_LIMB_BITS + LAST_LIMB_BITS == KEY_BITS,
    "limb widths must tile 256 bits exactly"
);

/// Width in bits of limb `j` (30 for the leading limbs, 16 for the last).
#[inline]
pub const fn limb_width(j: usize) -> u16 {
    if j < WIDE_LIMBS {
        WIDE_LIMB_BITS
    } else {
        LAST_LIMB_BITS
    }
}

/// MSB position of limb `j`'s top bit (its bit at offset 0 within the limb).
#[inline]
pub const fn limb_start(j: usize) -> u16 {
    (j as u16) * WIDE_LIMB_BITS
}

/// Locate global MSB bit position `d` (`d < 256`): returns
/// `(limb_index, limb_width, limb_start)`.
#[inline]
const fn locate(d: u16) -> (usize, u16, u16) {
    debug_assert!(d < KEY_BITS);
    if d < (WIDE_LIMBS as u16) * WIDE_LIMB_BITS {
        let j = (d / WIDE_LIMB_BITS) as usize;
        (j, WIDE_LIMB_BITS, (j as u16) * WIDE_LIMB_BITS)
    } else {
        (
            WIDE_LIMBS,
            LAST_LIMB_BITS,
            (WIDE_LIMBS as u16) * WIDE_LIMB_BITS,
        )
    }
}

/// Pack 32 big-endian bytes into 9 MSB-first limbs (D2).
///
/// Limb 0 holds bits `[0, 30)` (the most significant 30 key bits), limb 8
/// holds bits `[240, 256)` (the least significant 16). Bits are placed
/// MSB-aligned within each limb.
pub fn bytes_to_limbs(bytes: &[u8; KEY_BYTES]) -> Key {
    let mut limbs = [0u32; LIMBS];
    for d in 0..KEY_BITS {
        let bit = (bytes[(d / 8) as usize] >> (7 - (d % 8))) & 1;
        if bit == 0 {
            continue;
        }
        let (j, w, start) = locate(d);
        let off = d - start; // 0 == this limb's MSB
        limbs[j] |= 1u32 << (w - 1 - off);
    }
    limbs
}

/// Inverse of [`bytes_to_limbs`]. Requires each limb to be canonical
/// (`limb < 2^width`); higher bits are ignored.
pub fn limbs_to_bytes(limbs: &Key) -> [u8; KEY_BYTES] {
    let mut bytes = [0u8; KEY_BYTES];
    for d in 0..KEY_BITS {
        let (j, w, start) = locate(d);
        let off = d - start;
        let bit = (limbs[j] >> (w - 1 - off)) & 1;
        if bit != 0 {
            bytes[(d / 8) as usize] |= 1u8 << (7 - (d % 8));
        }
    }
    bytes
}

/// Bit of `limbs` at MSB position `d` (`d < 256`), returned as 0 or 1.
#[inline]
pub fn key_bit(limbs: &Key, d: u16) -> u32 {
    let (j, w, start) = locate(d);
    let off = d - start;
    (limbs[j] >> (w - 1 - off)) & 1
}

/// The `d`-bit region prefix of `limbs`, left-aligned and zero-filled below
/// bit `d` (D3). Equivalent to `(key >> (256 − d)) << (256 − d)`.
///
/// `d` ranges over `0..=256`; `d == 256` returns the key unchanged and
/// `d == 0` returns all zeros.
pub fn region_limbs(limbs: &Key, d: u16) -> Key {
    debug_assert!(d <= KEY_BITS);
    let mut out = [0u32; LIMBS];
    for j in 0..LIMBS {
        let w = limb_width(j);
        let start = limb_start(j);
        let end = start + w;
        if d >= end {
            out[j] = limbs[j];
        } else if d <= start {
            out[j] = 0;
        } else {
            // Boundary limb: keep the top `r = d - start` bits.
            let r = d - start;
            let drop = w - r; // low bits cleared
            out[j] = limbs[j] & !((1u32 << drop) - 1);
        }
    }
    out
}

/// True iff `region` is the canonical left-aligned encoding for depth `d`,
/// i.e. it carries no bits at or below position `d`.
#[inline]
pub fn is_canonical_region(region: &Key, d: u16) -> bool {
    region_limbs(region, d) == *region
}

/// Split a boundary limb of width `W` at intra-limb offset `r` (`0 ≤ r < W`)
/// into `(hi, beta, lo)` where, MSB-aligned:
///
/// ```text
///  ┌─────────── hi (r bits) ───────────┬ beta ┬─ lo (W−r−1 bits) ─┐
///  limb = hi·2^{W−r} + beta·2^{W−r−1} + lo
/// ```
///
/// `beta` is the side bit at position `r`; `hi` is the shared prefix above it
/// and `lo` the child-only tail below it. Shared by the tree, the witness
/// generator, and the AIR coherence block.
#[inline]
pub fn split_limb(limb: u32, w: u16, r: u16) -> (u32, u32, u32) {
    debug_assert!(r < w, "offset must leave room for the side bit");
    let lo_bits = w - r - 1;
    let hi = limb >> (w - r);
    let beta = (limb >> lo_bits) & 1;
    let lo = limb & ((1u32 << lo_bits) - 1);
    (hi, beta, lo)
}

/// First MSB bit position (`0..256`) at which `a` and `b` differ, or `256` if
/// they are equal. Mirrors `first_divergence` in `rsmt6a.py`.
pub fn first_divergence(a: &Key, b: &Key) -> u16 {
    for j in 0..LIMBS {
        let x = a[j] ^ b[j];
        if x != 0 {
            let w = limb_width(j);
            let start = limb_start(j);
            // Highest set bit of `x` counted from the limb LSB.
            let hb = 31 - x.leading_zeros() as u16;
            let off = (w - 1) - hb;
            return start + off;
        }
    }
    KEY_BITS
}

// -- BigUint bridges (tests / CLI only, per D2) -----------------------------

/// Convert a `BigUint` key (`< 2^256`) to 32 big-endian bytes.
pub fn biguint_to_bytes(k: &BigUint) -> [u8; KEY_BYTES] {
    let v = k.to_bytes_be();
    assert!(v.len() <= KEY_BYTES, "key exceeds 256 bits");
    let mut out = [0u8; KEY_BYTES];
    out[KEY_BYTES - v.len()..].copy_from_slice(&v);
    out
}

/// Convert a `BigUint` key to MSB-first limbs.
pub fn key_from_biguint(k: &BigUint) -> Key {
    bytes_to_limbs(&biguint_to_bytes(k))
}

/// Convert a `u128` (right-aligned, i.e. as the low 128 bits) to a key.
pub fn key_from_u128(k: u128) -> Key {
    let mut bytes = [0u8; KEY_BYTES];
    bytes[KEY_BYTES - 16..].copy_from_slice(&k.to_be_bytes());
    bytes_to_limbs(&bytes)
}

/// Convert limbs back to a `BigUint` (tests only).
pub fn key_to_biguint(limbs: &Key) -> BigUint {
    BigUint::from_bytes_be(&limbs_to_bytes(limbs))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_roundtrip() {
        let limbs = bytes_to_limbs(&[0u8; 32]);
        assert_eq!(limbs, [0u32; LIMBS]);
        assert_eq!(limbs_to_bytes(&limbs), [0u8; 32]);
    }

    #[test]
    fn top_bit_lands_in_limb0_msb() {
        let mut b = [0u8; 32];
        b[0] = 0x80; // MSB of the whole key
        let limbs = bytes_to_limbs(&b);
        assert_eq!(limbs[0], 1 << (WIDE_LIMB_BITS - 1));
        for l in &limbs[1..] {
            assert_eq!(*l, 0);
        }
        assert_eq!(key_bit(&limbs, 0), 1);
        assert_eq!(key_bit(&limbs, 1), 0);
    }

    #[test]
    fn low_bit_lands_in_limb8_lsb() {
        let mut b = [0u8; 32];
        b[31] = 0x01; // LSB of the whole key
        let limbs = bytes_to_limbs(&b);
        assert_eq!(limbs[8], 1);
        for l in &limbs[..8] {
            assert_eq!(*l, 0);
        }
        assert_eq!(key_bit(&limbs, 255), 1);
        assert_eq!(key_bit(&limbs, 254), 0);
    }

    #[test]
    fn bytes_limbs_roundtrip_random() {
        use rand::{RngExt, SeedableRng};
        use rand_xoshiro::Xoshiro256PlusPlus;
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(1);
        for _ in 0..1000 {
            let mut b = [0u8; 32];
            rng.fill(&mut b);
            let limbs = bytes_to_limbs(&b);
            for (j, l) in limbs.iter().enumerate() {
                assert!(*l < (1u32 << limb_width(j)), "limb {j} out of range");
            }
            assert_eq!(limbs_to_bytes(&limbs), b);
        }
    }

    #[test]
    fn key_bit_matches_biguint() {
        use rand::{RngExt, SeedableRng};
        use rand_xoshiro::Xoshiro256PlusPlus;
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(2);
        for _ in 0..200 {
            let mut b = [0u8; 32];
            rng.fill(&mut b);
            let limbs = bytes_to_limbs(&b);
            let n = BigUint::from_bytes_be(&b);
            for d in 0..KEY_BITS {
                // key_bit(k, d) = (k >> (256-1-d)) & 1
                let expect =
                    ((&n >> (KEY_BITS - 1 - d)) & BigUint::from(1u8)) == BigUint::from(1u8);
                assert_eq!(key_bit(&limbs, d) == 1, expect, "bit {d}");
            }
        }
    }

    #[test]
    fn region_matches_shift_definition() {
        use rand::{RngExt, SeedableRng};
        use rand_xoshiro::Xoshiro256PlusPlus;
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(3);
        for _ in 0..200 {
            let mut b = [0u8; 32];
            rng.fill(&mut b);
            let limbs = bytes_to_limbs(&b);
            let n = BigUint::from_bytes_be(&b);
            for d in 0..=KEY_BITS {
                let region = region_limbs(&limbs, d);
                // (n >> (256-d)) << (256-d)
                let sh = KEY_BITS - d;
                let expect = (&n >> sh) << sh;
                assert_eq!(key_to_biguint(&region), expect, "region d={d}");
                assert!(is_canonical_region(&region, d));
            }
        }
    }

    #[test]
    fn first_divergence_matches_definition() {
        use rand::{RngExt, SeedableRng};
        use rand_xoshiro::Xoshiro256PlusPlus;
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(4);
        for _ in 0..500 {
            let (mut ba, mut bb) = ([0u8; 32], [0u8; 32]);
            rng.fill(&mut ba);
            rng.fill(&mut bb);
            let a = bytes_to_limbs(&ba);
            let b = bytes_to_limbs(&bb);
            let fd = first_divergence(&a, &b);
            // brute force
            let mut expect = KEY_BITS;
            for d in 0..KEY_BITS {
                if key_bit(&a, d) != key_bit(&b, d) {
                    expect = d;
                    break;
                }
            }
            assert_eq!(fd, expect);
        }
    }

    #[test]
    fn split_limb_reconstructs() {
        for w in [30u16, 16] {
            for r in 0..w {
                let limb = 0x2AAAAAAA & ((1u32 << w) - 1);
                let (hi, beta, lo) = split_limb(limb, w, r);
                assert!(hi < (1u32 << r) || r == 0 && hi == 0);
                assert!(beta <= 1);
                let recon = (hi << (w - r)) + (beta << (w - r - 1)) + lo;
                assert_eq!(recon, limb, "w={w} r={r}");
            }
        }
    }
}
