//! Adversarial tamper harness — verification-plan §4.
//!
//! Each helper applies a specific mutation to one or more traces. A passing
//! test asserts that `prove_and_verify_inner` reports `Err`, demonstrating
//! that the modified witness fails either constraint validation or LogUp
//! multiset balance.
//!
//! Column offsets here mirror the `const C_*` definitions in
//! `rsmt-air/src/table_{a,f,c}.rs`; if those layouts change, update both.

use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;

use crate::batch_demo::{Traces, prove_and_verify_inner};

type F = BabyBear;

// Table A column offsets (mirror of crate::table_a).
const A_W: usize = 24;
const A_C_DEPTH: usize = 3;
const A_C_NEW_HASH: usize = 13;
const A_C_OLD_IS_NONE: usize = 21;

// Table F column offsets (mirror of crate::table_f).
const F_W: usize = 74;
const F_C_DEPTH: usize = 3;
const F_C_LEFT_NEW: usize = 12;
const F_C_RIGHT_NEW: usize = 29;
const F_C_PARENT_NEW: usize = 46;
const F_C_B11: usize = 57;
const F_C_PARENT_NEW_TAIL: usize = 66;

// Table C column offsets.
const C_W: usize = 50;
const C_STATE_OUT: usize = 18 + 16; // key[9] + value[9] + state_in[16]

fn cell_mut(t: &mut RowMajorMatrix<F>, row: usize, col: usize) -> &mut F {
    let w = t.width;
    &mut t.values[row * w + col]
}

fn first_real_a_row(a: &RowMajorMatrix<F>, predicate: impl Fn(&[F]) -> bool) -> Option<usize> {
    let w = a.width;
    let h = a.values.len() / w;
    (0..h).find(|&i| predicate(&a.values[i * w..(i + 1) * w]))
}

/// Class 1: swap left and right child slots in an F row.
pub fn run_swap_left_right(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        // Swap the new-hash digests on row 0 of F.
        for j in 0..8 {
            let l = *cell_mut(t.f, 0, F_C_LEFT_NEW + j);
            let r = *cell_mut(t.f, 0, F_C_RIGHT_NEW + j);
            *cell_mut(t.f, 0, F_C_LEFT_NEW + j) = r;
            *cell_mut(t.f, 0, F_C_RIGHT_NEW + j) = l;
        }
    })
}

/// Class 2: duplicate a child row by copying row N into row N+1 in Table A.
pub fn run_duplicate_a_row(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        let w = t.a.width;
        let src = 1usize;
        let dst = 2usize;
        let row: Vec<F> = t.a.values[src * w..(src + 1) * w].to_vec();
        for (j, v) in row.into_iter().enumerate() {
            t.a.values[dst * w + j] = v;
        }
    })
}

/// Class 3: change `depth` on an F row while keeping all hashes fixed.
/// Bumps the Bus 2 input tuple so the Poseidon2 lookup no longer matches.
pub fn run_depth_mismatch(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        *cell_mut(t.f, 0, F_C_DEPTH) += F::ONE;
    })
}

/// Class 4: forge `old_is_none` on a Table A row.
pub fn run_forge_old_is_none(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        let target = first_real_a_row(t.a, |row| row[A_C_OLD_IS_NONE].is_zero()).unwrap_or(0);
        *cell_mut(t.a, target, A_C_OLD_IS_NONE) = F::ONE;
    })
}

/// Class 5: corrupt the four-way passthrough by bumping `parent_new[0]` on
/// a passthrough F row. The local constraint
/// `(1 - b11) * parent_new[j] = b01 * right_new[j] + b10 * left_new[j]`
/// must reject the mismatch.
pub fn run_break_passthrough(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        let w = t.f.width;
        let h = t.f.values.len() / w;
        // First real row with b11=0 is a passthrough.
        for r in 0..h {
            if t.f.values[r * w + F_C_B11] == F::ZERO && t.f.values[r * w + F_C_LEFT_NEW] != F::ZERO
            {
                *cell_mut(t.f, r, F_C_PARENT_NEW) += F::ONE;
                return;
            }
        }
        *cell_mut(t.f, 0, F_C_PARENT_NEW) += F::ONE;
    })
}

/// Class 6: reuse a permutation result by overwriting Table C's final
/// state_out digest with another row's. Bus 4 should reject the mismatch.
pub fn run_reuse_perm_result(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        let w = t.c.width;
        // Row 2 (first leaf, last sponge step) -> overwrite digest with row 5 (second leaf).
        if t.c.values.len() < 6 * w {
            // Single-leaf batch — skip
            return;
        }
        for j in 0..8 {
            *cell_mut(t.c, 2, C_STATE_OUT + j) = t.c.values[5 * w + C_STATE_OUT + j];
        }
    })
}

/// Class 7: tamper a Poseidon2 output tail in Table F. The tail is not
/// covered by any local constraint — only Bus 2 catches it.
pub fn run_tamper_f_tail(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        let w = t.f.width;
        let h = t.f.values.len() / w;
        for r in 0..h {
            if t.f.values[r * w + F_C_B11] == F::ONE {
                *cell_mut(t.f, r, F_C_PARENT_NEW_TAIL) += F::ONE;
                return;
            }
        }
        // Fallback: tamper row 0 if no b11 row found.
        *cell_mut(t.f, 0, F_C_PARENT_NEW_TAIL) += F::ONE;
    })
}

/// Class 8: scramble an A-row digest. Breaks both the local constraints and
/// the tree/parent buses depending on which row we hit.
pub fn run_scramble_a_digest(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        // Bump first limb of new_hash on A row 0.
        *cell_mut(t.a, 0, A_C_NEW_HASH) += F::ONE;
    })
}

/// Class 9: tamper Table E's multiplicity column. Bus 5 multiset balance
/// must reject any inconsistency between A's depth receives and E's sends.
pub fn run_break_e_multiplicity(seed: u64, batch: usize) -> Result<(), ()> {
    prove_and_verify_inner(seed, batch, |t: &mut Traces<'_>| {
        // Increment the multiplicity for byte 0 (always present at row 0).
        t.e.values[0] += F::ONE;
    })
}

const _: () = assert!(A_W == rsmt_air::TABLE_A_WIDTH);
const _: () = assert!(F_W == rsmt_air::TABLE_F_WIDTH);
const _: () = assert!(C_W == rsmt_air::TABLE_C_WIDTH);
const _: () = assert!(F_C_DEPTH < F_W);
const _: () = assert!(F_C_PARENT_NEW < F_W);
const _: () = assert!(A_C_DEPTH < A_W);

#[cfg(test)]
mod tests {
    use super::*;

    const SEED: u64 = 11;
    const BATCH: usize = 16;

    #[test]
    fn swap_left_right_rejected() {
        assert!(run_swap_left_right(SEED, BATCH).is_err());
    }

    #[test]
    fn duplicate_a_row_rejected() {
        assert!(run_duplicate_a_row(SEED, BATCH).is_err());
    }

    #[test]
    fn depth_mismatch_rejected() {
        assert!(run_depth_mismatch(SEED, BATCH).is_err());
    }

    #[test]
    fn forge_old_is_none_rejected() {
        assert!(run_forge_old_is_none(SEED, BATCH).is_err());
    }

    #[test]
    fn break_passthrough_rejected() {
        assert!(run_break_passthrough(SEED, BATCH).is_err());
    }

    #[test]
    fn reuse_perm_result_rejected() {
        assert!(run_reuse_perm_result(SEED, BATCH).is_err());
    }

    #[test]
    fn tamper_f_tail_rejected() {
        assert!(run_tamper_f_tail(SEED, BATCH).is_err());
    }

    #[test]
    fn scramble_a_digest_rejected() {
        assert!(run_scramble_a_digest(SEED, BATCH).is_err());
    }

    #[test]
    fn break_e_multiplicity_rejected() {
        assert!(run_break_e_multiplicity(SEED, BATCH).is_err());
    }
}
