//! Adversarial tamper harness (DEVPLAN M5, verification-plan §4).
//!
//! Each class mutates a freshly-built main trace through the
//! [`prove_and_verify_round_with`] hook and asserts the round is **rejected** —
//! by a local AIR constraint or by a LogUp multiset imbalance. Together they
//! exercise the soundness-critical wiring: digest bindings (Bus 2/3/4), the
//! post-order `subtree_start` chain (Bus 1, D19), and the range/pow2 tables.
//!
//! Column offsets mirror the `ACols`/`FCols`/`CMainCols` field order in
//! `rsmt-air/src/table_{a,f,c}.rs`; the `assert!`s below pin the widths so a
//! layout change fails to compile here rather than silently miswiring a test.

use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

use rand::{RngExt, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

use rsmt_core::{Key, KeyValue, Tree, bytes_to_limbs};
use rsmt_hash::Poseidon2Hasher;
use rsmt_witness::{TracePlan, build_plan};

use crate::config::ProverConfig;
use crate::proof_hash::Poseidon2ProofHash;
use crate::round::{RoundTraces, prove_and_verify_round_with};

type F = BabyBear;

// -- Table A column offsets (mirror crate::table_a::ACols, width 37) ----------
const A_W: usize = 37;
const A_NEW: usize = 13; // new[13..21]
const A_OLD_IS_NONE: usize = 21;
const A_SUBTREE_START: usize = 36;

// -- Table F column offsets (mirror crate::table_f::FCols, width 142) ---------
const F_W: usize = 142;
const F_LS: usize = 1;
const F_RS: usize = 2;
const F_DEPTH: usize = 3;
const F_L_NEW: usize = 44;
const F_R_NEW: usize = 76;
const F_B11: usize = 102;
const F_PARENT_NEW: usize = 112; // propagated new-node digest
const F_MID: usize = 126; // shared prefix output, bound only by the Bus-2 prefix receive

const _: () = assert!(A_W == rsmt_air::TABLE_A_WIDTH);
const _: () = assert!(F_W == rsmt_air::TABLE_F_WIDTH);
const _: () = assert!(A_SUBTREE_START < A_W && F_MID + 16 <= F_W);

fn rand_key(rng: &mut Xoshiro256PlusPlus) -> Key {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    bytes_to_limbs(&b)
}

/// A two-round plan rich in opcodes (S, O, OL, L, N) over a prefilled tree.
fn rich_plan(seed: u64, prefill: usize, batch: usize) -> TracePlan {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(seed);
    let mut tree: Tree<Poseidon2Hasher> = Tree::new();
    let b1: Vec<KeyValue> = (0..prefill)
        .map(|_| (rand_key(&mut rng), vec![1u8; 8]))
        .collect();
    tree.batch_insert(b1);
    let old = tree.root_hash();
    let b2: Vec<KeyValue> = (0..batch)
        .map(|_| (rand_key(&mut rng), vec![2u8; 8]))
        .collect();
    let (applied, proof) = tree.batch_insert(b2);
    let new = tree.root_hash().unwrap();
    build_plan(&proof, &applied, old.as_ref(), &new).unwrap()
}

/// Run one round with `tamper` applied to the traces; `Ok` means the proof
/// verified (an escaped mutation), `Err` means it was rejected.
fn run(tamper: impl FnOnce(&mut RoundTraces<'_>)) -> Result<(), String> {
    let plan = rich_plan(7, 48, 24);
    let cfg = ProverConfig::default();
    prove_and_verify_round_with::<Poseidon2ProofHash>(&plan, 7, &cfg, tamper)
}

/// First row of `t` (width `w`) satisfying `pred`.
fn find_row(vals: &[F], w: usize, pred: impl Fn(&[F]) -> bool) -> Option<usize> {
    (0..vals.len() / w).find(|&i| pred(&vals[i * w..(i + 1) * w]))
}

// -- classes ------------------------------------------------------------------

/// Swap left/right child digests on an F join row — the node-sponge children
/// block (Bus 2) and the parent digest no longer agree.
pub fn swap_left_right() -> Result<(), String> {
    // Row 0 of F is a join row (joins are the leading segment).
    run(|t| {
        for j in 0..8 {
            t.f.values.swap(F_L_NEW + j, F_R_NEW + j);
        }
    })
}

/// Bump `depth` on an F row while keeping hashes fixed → Bus 2 prefix input and
/// the R10 range receives both diverge.
pub fn tamper_depth() -> Result<(), String> {
    run(|t| t.f.values[F_DEPTH] += F::ONE)
}

/// Forge `old_is_none` on a Table A row where it was false.
pub fn forge_old_is_none() -> Result<(), String> {
    run(|t| {
        let w = t.a.width;
        // S/O/OL rows (cols 0/1/2) are constrained old_is_none = 0.
        let row = find_row(&t.a.values, w, |r| {
            r[A_OLD_IS_NONE] == F::ZERO && (r[0] + r[1] + r[2]) != F::ZERO
        })
        .unwrap_or(0);
        t.a.values[row * w + A_OLD_IS_NONE] = F::ONE;
    })
}

/// Scramble an A-row `new` digest limb → local digest rules and the parent/tree
/// buses reject.
pub fn scramble_a_digest() -> Result<(), String> {
    run(|t| t.a.values[A_NEW] += F::ONE)
}

/// D19: corrupt a base opcode's `subtree_start` (row 0 is a leaf, start = 0).
/// Breaks the base constraint and the Bus-1 post-order chain.
pub fn tamper_subtree_start() -> Result<(), String> {
    run(|t| t.a.values[A_SUBTREE_START] += F::ONE)
}

/// D19: corrupt a join's right-child start `rs` → the left-child Bus-1 receive
/// key (`rs − 1`) points at the wrong row, breaking the tree multiset.
pub fn tamper_join_rs() -> Result<(), String> {
    run(|t| t.f.values[F_RS] += F::ONE)
}

/// D19: corrupt a join's left/parent start `ls` → Bus 3 send to A's N row and
/// the left-child Bus-1 receive disagree.
pub fn tamper_join_ls() -> Result<(), String> {
    run(|t| t.f.values[F_LS] += F::ONE)
}

/// Tamper the shared node-sponge prefix output `mid` — bound only by the Bus-2
/// prefix receive (D17), so this isolates the permutation lookup.
pub fn tamper_perm_prefix() -> Result<(), String> {
    run(|t| {
        let w = t.f.width;
        let row = find_row(&t.f.values, w, |r| r[F_B11] == F::ONE).unwrap_or(0);
        t.f.values[row * w + F_MID + 8] += F::ONE;
    })
}

/// D17: forge a join's propagated new-node digest `parent_new`. The tagged
/// Bus-2 terminal receive now takes the digest from this column, binding it to
/// the real Poseidon2 output — so a forgery breaks the children-block lookup.
pub fn forge_parent_new() -> Result<(), String> {
    run(|t| t.f.values[F_PARENT_NEW] += F::ONE)
}

/// Inflate a Table R send multiplicity → the range bus over-sends and no
/// receiver matches.
pub fn tamper_range_mult() -> Result<(), String> {
    run(|t| t.r.values[0] += F::ONE)
}

/// Inflate a Table P send multiplicity → the pow2 bus imbalance.
pub fn tamper_pow2_mult() -> Result<(), String> {
    run(|t| t.p.values[0] += F::ONE)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    /// A tampered witness is *rejected* if it cannot yield a verifying proof.
    /// That surfaces two equivalent ways: the prover's built-in `check_constraints`
    /// pass panics on the violated constraint (debug builds), or — when only the
    /// global LogUp balance is off — `verify_batch` returns `Err`. Either is a
    /// rejection; only a clean `Ok` is a soundness escape. We silence the panic
    /// hook so an expected constraint panic doesn't spam the test log.
    fn rejected(f: impl FnOnce() -> Result<(), String>) -> bool {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let r = catch_unwind(AssertUnwindSafe(f));
        std::panic::set_hook(prev);
        !matches!(r, Ok(Ok(())))
    }

    #[test]
    fn honest_round_verifies() {
        // The identity hook must still prove+verify (guards against a harness
        // that rejects everything, which would make the classes vacuous).
        assert!(run(|_| {}).is_ok(), "honest round must verify");
    }

    macro_rules! rejects {
        ($name:ident, $f:path) => {
            #[test]
            fn $name() {
                assert!(rejected($f), "tamper class must be rejected");
            }
        };
    }

    rejects!(swap_left_right_rejected, swap_left_right);
    rejects!(tamper_depth_rejected, tamper_depth);
    rejects!(forge_old_is_none_rejected, forge_old_is_none);
    rejects!(scramble_a_digest_rejected, scramble_a_digest);
    rejects!(tamper_subtree_start_rejected, tamper_subtree_start);
    rejects!(tamper_join_rs_rejected, tamper_join_rs);
    rejects!(tamper_join_ls_rejected, tamper_join_ls);
    rejects!(tamper_perm_prefix_rejected, tamper_perm_prefix);
    rejects!(forge_parent_new_rejected, forge_parent_new);
    rejects!(tamper_range_mult_rejected, tamper_range_mult);
    rejects!(tamper_pow2_mult_rejected, tamper_pow2_mult);
}
