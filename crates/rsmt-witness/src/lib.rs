//! Out-of-circuit preprocessing (DEVPLAN M2).
//!
//! Lowers a Poseidon2 consistency-proof stream into a [`TracePlan`]: all
//! data-dependent computation (post-order pointers, case bits, derived
//! regions, the boundary-limb coherence split, the deduplicated permutation
//! arena, and multiplicity tallies) happens here, so M3's trace generation is
//! a straight parallel fill. The plan is self-validated against the reference
//! verifier before it is trusted.

pub mod plan;
pub mod r10;

pub use plan::{
    ARow, Arena, CLeaf, ChildCoh, DRow, FJoin, FOpen, LeafKind, OpKind, PlanError, Publics, Shape,
    TracePlan, build_plan, check_plan_invariants,
};

#[cfg(test)]
mod tests;
