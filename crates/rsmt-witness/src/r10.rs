//! Radix-1024 range decomposition (DEVPLAN R2, D12/D13).
//!
//! All witness-side helpers for proving `x < 2^k` against Table R
//! (`R10 = {(bits, value) : 0 ≤ bits ≤ 10, value < 2^bits}`). Two flavours:
//!
//! - **Canonical (fixed-width)** [`canonical_limb`]: a key/region/value limb of
//!   width `W ∈ {30, 16}` decomposes into `⌈W/10⌉` digits, each looked up at its
//!   fixed width. This proves the limb is a genuine `W`-bit value (closes the
//!   finding-5 input-canonicality gap).
//! - **Variable-width** [`variable_range`]: for the coherence prefix/tail
//!   `x < 2^k` with `k` data-dependent, a one-hot selects the boundary digit;
//!   digits below it are full 10-bit, the boundary digit is `s`-bit, digits
//!   above are forced zero. No complement, no wide multiply.
//!
//! Every emitted `(bits, value)` pair is a Table-R receive; the range bus
//! balances iff Table R's per-entry `mult` equals the total emitted count.

/// Maximum digit width (radix-1024 ⇒ 10-bit digits).
pub const R10_MAX_BITS: u32 = 10;
/// Number of real Table-R rows: `Σ_{b=0}^{10} 2^b = 2^11 − 1`.
pub const R10_REAL: usize = (1 << (R10_MAX_BITS + 1)) - 1;

/// Canonical `(bits, value)` enumeration, in row order.
pub fn r10_rows() -> impl Iterator<Item = (u32, u32)> {
    (0..=R10_MAX_BITS).flat_map(|bits| (0..(1u32 << bits)).map(move |v| (bits, v)))
}

/// Row index of `(bits, value)` in the R10 enumeration.
#[inline]
pub fn r10_index(bits: u32, value: u32) -> usize {
    debug_assert!(bits <= R10_MAX_BITS && value < (1 << bits));
    ((1usize << bits) - 1) + value as usize
}

/// Radix-1024 digits of `x`, little-endian, exactly `n` digits.
pub fn radix1024(x: u32, n: usize) -> Vec<u32> {
    let mut d = Vec::with_capacity(n);
    let mut v = x;
    for _ in 0..n {
        d.push(v & 0x3FF);
        v >>= 10;
    }
    debug_assert_eq!(v, 0, "value {x} does not fit in {n} radix-1024 digits");
    d
}

/// Number of radix-1024 digits for a `w`-bit value (`⌈w/10⌉`).
#[inline]
pub fn n_digits(w: u16) -> usize {
    w.div_ceil(10) as usize
}

/// Width (in bits) of digit `i` for a canonical `w`-bit limb: 10 for the low
/// digits, `w − 10·(n−1)` for the top digit.
#[inline]
pub fn canonical_digit_width(w: u16, i: usize, n: usize) -> u16 {
    if i + 1 < n {
        10
    } else {
        w - 10 * (n as u16 - 1)
    }
}

/// Canonical decomposition of a `w`-bit limb: returns `(digits, receives)`
/// where `receives[i] = (width_i, digits[i])` is the Table-R lookup that proves
/// digit `i` is within its width. Proves `limb < 2^w` exactly.
pub fn canonical_limb(limb: u32, w: u16) -> (Vec<u32>, Vec<(u32, u32)>) {
    let n = n_digits(w);
    let digits = radix1024(limb, n);
    let receives = digits
        .iter()
        .enumerate()
        .map(|(i, &d)| (canonical_digit_width(w, i, n) as u32, d))
        .collect();
    (digits, receives)
}

/// Variable-width range check `x < 2^k` (`k ≤ 30`). Returns:
/// - `digits[3]`: radix-1024 digits of `x` (over 30 bits);
/// - `u[3]`: one-hot selecting the boundary digit `h = k / 10`;
/// - `s`: the boundary offset `k mod 10`;
/// - `receives[3]`: `(width_i, digits[i])` Table-R lookups, where `width_i` is
///   `10` for `i < h`, `s` for `i = h`, and `0` for `i > h` (forcing high
///   digits to zero, since `(0, d)` is in R10 only for `d = 0`).
pub struct VarRange {
    pub digits: [u32; 3],
    pub u: [bool; 3],
    pub s: u16,
    pub receives: [(u32, u32); 3],
}

pub fn variable_range(x: u32, k: u16) -> VarRange {
    // Coherence bounds satisfy `k = W−r−1 ≤ 29` and `r ≤ 29`, so the boundary
    // digit `h = k/10 ≤ 2` fits the 3-wide one-hot. (30-bit canonical limbs use
    // `canonical_limb`, not this.)
    debug_assert!(
        k <= 29 && x < (1u32 << k) || (k == 0 && x == 0),
        "x={x} not < 2^{k}"
    );
    let h = (k / 10) as usize;
    let s = k % 10;
    let d = radix1024(x, 3);
    let digits = [d[0], d[1], d[2]];
    let u = [h == 0, h == 1, h == 2];
    let width = |i: usize| -> u32 {
        match i.cmp(&h) {
            std::cmp::Ordering::Less => 10,
            std::cmp::Ordering::Equal => s as u32,
            std::cmp::Ordering::Greater => 0,
        }
    };
    let receives = [
        (width(0), digits[0]),
        (width(1), digits[1]),
        (width(2), digits[2]),
    ];
    VarRange {
        digits,
        u,
        s,
        receives,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn radix_roundtrip() {
        for x in [0u32, 1, 1023, 1024, (1 << 30) - 1, 0x2AAAAAAA] {
            let d = radix1024(x, 3);
            let recon = d[0] + (d[1] << 10) + (d[2] << 20);
            assert_eq!(recon, x);
            for dd in d {
                assert!(dd < 1024);
            }
        }
    }

    #[test]
    fn canonical_widths() {
        // 30-bit limb: three 10-bit digits.
        let (d, r) = canonical_limb((1 << 30) - 1, 30);
        assert_eq!(d.len(), 3);
        assert!(r.iter().all(|&(w, _)| w == 10));
        // 16-bit limb: 10-bit + 6-bit.
        let (d, r) = canonical_limb((1 << 16) - 1, 16);
        assert_eq!(d.len(), 2);
        assert_eq!(r[0].0, 10);
        assert_eq!(r[1].0, 6);
        assert!(r[1].1 < 64);
    }

    #[test]
    fn variable_range_reconstructs_and_bounds() {
        for k in 0u16..=29 {
            let max = (1u32 << k) - 1;
            for &x in &[0u32, max, max / 2, max / 3] {
                let vr = variable_range(x, k);
                let recon = vr.digits[0] + (vr.digits[1] << 10) + (vr.digits[2] << 20);
                assert_eq!(recon, x, "k={k} x={x}");
                assert_eq!(vr.u.iter().filter(|b| **b).count(), 1); // one-hot
                // each receive is a valid R10 entry: digit < 2^width.
                for (w, d) in vr.receives {
                    assert!(d < (1u32 << w), "digit {d} ≥ 2^{w} (k={k} x={x})");
                }
            }
        }
    }
}
