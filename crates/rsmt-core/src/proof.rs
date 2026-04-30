//! Post-order opcode stream + stack-machine verifier.

use num_bigint::BigUint;

use crate::hasher::Hasher;
use crate::sort_key::get_sort_key;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op<D> {
    /// Unchanged subtree. `None` denotes the empty subtree.
    S(Option<D>),
    /// Newly inserted leaf — pops the next element from the sorted batch.
    L,
    /// Internal node at the given bifurcation depth. Two children precede.
    N(u8),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    BadOpcode,
    StackUnderflow,
    BatchExhausted,
    LeftoverBatch,
    LeftoverProof,
    BadFinalStack,
    RootMismatch,
}

/// Stack-machine verifier (post-order). Returns `Ok(())` iff `proof` rebuilds
/// `(old_root, new_root)` from `batch` exactly.
pub fn verify_consistency<H: Hasher>(
    proof: &[Op<H::Digest>],
    old_root: Option<&H::Digest>,
    new_root: &H::Digest,
    batch: &[(BigUint, Vec<u8>)],
) -> Result<(), VerifyError> {
    if batch.is_empty() {
        // Empty batch: must be a single S that matches old_root == new_root.
        return match (old_root, proof) {
            (or, [Op::S(h)]) if h.as_ref() == or && or.map_or(true, |r| r == new_root) => Ok(()),
            _ => Err(VerifyError::RootMismatch),
        };
    }

    let mut sorted: Vec<&(BigUint, Vec<u8>)> = batch.iter().collect();
    sorted.sort_by(|a, b| get_sort_key(&a.0).cmp(&get_sort_key(&b.0)));

    let mut stack: Vec<(Option<H::Digest>, H::Digest)> = Vec::new();
    let mut bi = 0usize;

    for op in proof {
        match op {
            Op::S(h) => {
                let Some(h) = h.clone() else {
                    return Err(VerifyError::BadOpcode);
                };
                stack.push((Some(h.clone()), h));
            }
            Op::L => {
                if bi >= sorted.len() {
                    return Err(VerifyError::BatchExhausted);
                }
                let (k, v) = sorted[bi];
                bi += 1;
                stack.push((None, H::hash_leaf(k, v)));
            }
            Op::N(depth) => {
                let (rh0, rh1) = stack.pop().ok_or(VerifyError::StackUnderflow)?;
                let (lh0, lh1) = stack.pop().ok_or(VerifyError::StackUnderflow)?;
                let h0 = match (lh0, rh0) {
                    (None, None) => None,
                    (None, Some(r)) => Some(r),
                    (Some(l), None) => Some(l),
                    (Some(l), Some(r)) => Some(H::hash_node(&l, &r, *depth)),
                };
                let h1 = H::hash_node(&lh1, &rh1, *depth);
                stack.push((h0, h1));
            }
        }
    }

    if bi != sorted.len() {
        return Err(VerifyError::LeftoverBatch);
    }
    if stack.len() != 1 {
        return Err(VerifyError::BadFinalStack);
    }
    let (r0, r1) = stack.pop().unwrap();
    if r0.as_ref() != old_root {
        return Err(VerifyError::RootMismatch);
    }
    if &r1 != new_root {
        return Err(VerifyError::RootMismatch);
    }
    Ok(())
}
