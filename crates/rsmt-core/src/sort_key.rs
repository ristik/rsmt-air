//! LSB-first traversal sort key. Mirrors `get_sort_key` in `ndrsmt3o.py`.

use num_bigint::BigUint;

const BIT_REVERSE_TABLE: [u8; 256] = {
    let mut t = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        let b = i as u8;
        let r = ((b & 0x01) << 7)
            | ((b & 0x02) << 5)
            | ((b & 0x04) << 3)
            | ((b & 0x08) << 1)
            | ((b & 0x10) >> 1)
            | ((b & 0x20) >> 3)
            | ((b & 0x40) >> 5)
            | ((b & 0x80) >> 7);
        t[i] = r;
        i += 1;
    }
    t
};

pub const KEY_BYTES: usize = 32;

pub fn key_to_bytes_be(k: &BigUint) -> [u8; KEY_BYTES] {
    let v = k.to_bytes_be();
    assert!(v.len() <= KEY_BYTES, "key exceeds 256 bits");
    let mut out = [0u8; KEY_BYTES];
    out[KEY_BYTES - v.len()..].copy_from_slice(&v);
    out
}

/// LSB-first sort key: reverse byte order, then bit-reverse each byte.
pub fn get_sort_key(k: &BigUint) -> [u8; KEY_BYTES] {
    let be = key_to_bytes_be(k);
    let mut out = [0u8; KEY_BYTES];
    for i in 0..KEY_BYTES {
        out[i] = BIT_REVERSE_TABLE[be[KEY_BYTES - 1 - i] as usize];
    }
    out
}
