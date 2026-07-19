//! Occurrence-correct permutation plan (R3-D7, finding §4;
//! `docs/r3/04-soundness-budget.md` §5, `02-relation-and-extraction.md` S8).
//!
//! The legacy [`crate::plan::Arena`] deduplicates equal Poseidon2 inputs via a
//! `HashMap` while Table B sends each stored row with multiplicity **one**. Two
//! logical receives of one equal tuple would then be backed by a single send,
//! breaking completeness. This plan instead stores **one entry per logical
//! evaluation occurrence** and never deduplicates, so every consumer receive is
//! backed by its own send.
//!
//! Occurrences are segmented by Bus-2 mode into `feed_forward` (whose full
//! 16-limb output feeds another sponge block: leaf steps 0/1, node prefixes) and
//! `terminal` (whose 8-limb digest is the only output used: leaf step 2, node
//! children blocks). This scalar segmentation makes Table B preprocessing a
//! function of `(n_ff, n_term)` only — no `RoundShape::b_modes: Vec<bool>`.
//!
//! The intentional single exception (S8) is the join **prefix**: it is one
//! feed-forward occurrence whose `mid` is referenced *locally* by both the new
//! and (for `b11`) old children blocks of the same junction. That is one send
//! used twice locally within one J row, not a deduplicated cross-row share.

use rsmt_hash::PermIo;

/// A segmented, occurrence-correct record of every Poseidon2 evaluation.
#[derive(Default, Debug, Clone)]
pub struct PermutationPlan {
    feed_forward: Vec<PermIo>,
    terminal: Vec<PermIo>,
}

/// Arena indices for one leaf's three permutations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeafPermIdx {
    /// Feed-forward index of leaf step 0.
    pub ff0: u32,
    /// Feed-forward index of leaf step 1.
    pub ff1: u32,
    /// Terminal index of leaf step 2 (the digest).
    pub term: u32,
}

/// Arena indices for one junction's permutations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JoinPermIdx {
    /// Feed-forward index of the shared node prefix.
    pub prefix: u32,
    /// Terminal index of the new children block (always present).
    pub new_children: u32,
    /// Terminal index of the old children block, `Some` iff `b11`.
    pub old_children: Option<u32>,
}

/// Arena indices for one opening's permutations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpenPermIdx {
    /// Feed-forward index of the node prefix.
    pub prefix: u32,
    /// Terminal index of the node children block (the digest).
    pub node: u32,
}

impl PermutationPlan {
    pub fn new() -> Self {
        Self::default()
    }

    /// Append one feed-forward occurrence, returning its index in that segment.
    pub fn push_ff(&mut self, io: PermIo) -> u32 {
        let i = self.feed_forward.len() as u32;
        self.feed_forward.push(io);
        i
    }

    /// Append one terminal occurrence, returning its index in that segment.
    pub fn push_term(&mut self, io: PermIo) -> u32 {
        let i = self.terminal.len() as u32;
        self.terminal.push(io);
        i
    }

    /// Record one leaf's three permutations (2 feed-forward + 1 terminal).
    pub fn record_leaf(&mut self, ios: [PermIo; 3]) -> LeafPermIdx {
        LeafPermIdx {
            ff0: self.push_ff(ios[0]),
            ff1: self.push_ff(ios[1]),
            term: self.push_term(ios[2]),
        }
    }

    /// Record one junction: the shared prefix (feed-forward), the new children
    /// block (terminal), and — iff `b11` — the old children block (terminal).
    pub fn record_join(
        &mut self,
        prefix: PermIo,
        new_children: PermIo,
        old_children: Option<PermIo>,
    ) -> JoinPermIdx {
        JoinPermIdx {
            prefix: self.push_ff(prefix),
            new_children: self.push_term(new_children),
            old_children: old_children.map(|io| self.push_term(io)),
        }
    }

    /// Record one opening: the node prefix (feed-forward) and the node children
    /// block (terminal).
    pub fn record_open(&mut self, prefix: PermIo, node: PermIo) -> OpenPermIdx {
        OpenPermIdx {
            prefix: self.push_ff(prefix),
            node: self.push_term(node),
        }
    }

    pub fn feed_forward(&self) -> &[PermIo] {
        &self.feed_forward
    }

    pub fn terminal(&self) -> &[PermIo] {
        &self.terminal
    }

    /// Feed-forward occurrence count (`n_p2ff`).
    pub fn n_ff(&self) -> usize {
        self.feed_forward.len()
    }

    /// Terminal occurrence count (`n_p2term`).
    pub fn n_term(&self) -> usize {
        self.terminal.len()
    }

    /// Total logical permutation count (`n_perm = n_ff + n_term`).
    pub fn n_perm(&self) -> usize {
        self.n_ff() + self.n_term()
    }

    /// The Table-B occurrence order: feed-forward segment then terminal segment.
    /// Table B sends the first segment on `p2ff` and the second on `p2term`;
    /// padding lanes have zero multiplicity.
    pub fn table_b_order(&self) -> impl Iterator<Item = &PermIo> {
        self.feed_forward.iter().chain(self.terminal.iter())
    }

    /// Assert the exact occurrence identities against the round's opcode counts
    /// (`04-soundness-budget.md` §4/§5). Returns `Err` with a static reason on
    /// any mismatch — a hard invariant, not a heuristic.
    pub fn verify_counts(
        &self,
        n_leaf: usize,
        n_join: usize,
        n_open: usize,
        n_b11: usize,
    ) -> Result<(), &'static str> {
        if n_b11 > n_join {
            return Err("n_b11 exceeds n_join");
        }
        let expect_ff = 2 * n_leaf + n_join + n_open;
        let expect_term = n_leaf + n_join + n_b11 + n_open;
        if self.n_ff() != expect_ff {
            return Err("feed-forward occurrence count mismatch");
        }
        if self.n_term() != expect_term {
            return Err("terminal occurrence count mismatch");
        }
        // n_perm = 3·n_leaf + 2·n_join + n_b11 + 2·n_open
        if self.n_perm() != 3 * n_leaf + 2 * n_join + n_b11 + 2 * n_open {
            return Err("total permutation count mismatch");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use rsmt_hash::{State, default_perm, leaf_perm_io, node_children_io, node_prefix_io};

    fn zero_io() -> PermIo {
        PermIo {
            input: [p3_baby_bear::BabyBear::ZERO; 16],
            output: [p3_baby_bear::BabyBear::ZERO; 16],
        }
    }

    #[test]
    fn occurrences_are_not_deduplicated() {
        // Two identical logical permutation inputs whose required multiplicity is
        // two (finding §4). The legacy HashMap arena would collapse them to one
        // entry; the occurrence plan keeps both, so Table B sends the tuple twice
        // and each of the two receives is backed by its own send.
        let mut plan = PermutationPlan::new();
        let io = zero_io();
        let a = plan.push_term(io);
        let b = plan.push_term(io);
        assert_ne!(a, b, "equal inputs must get distinct occurrence slots");
        assert_eq!(plan.n_term(), 2, "both occurrences stored (no dedup)");
        assert_eq!(plan.terminal()[a as usize], plan.terminal()[b as usize]);
    }

    #[test]
    fn segmentation_and_counts_match_identities() {
        let perm = default_perm();
        let mut plan = PermutationPlan::new();

        // One leaf.
        let key: State = core::array::from_fn(|i| p3_baby_bear::BabyBear::from_u32(i as u32));
        let key9 = core::array::from_fn(|i| key[i]);
        let val9 = core::array::from_fn(|i| key[i + 1]);
        let leaf = plan.record_leaf(leaf_perm_io(&perm, &key9, &val9));
        assert_eq!(
            leaf,
            LeafPermIdx {
                ff0: 0,
                ff1: 1,
                term: 0
            }
        );

        // One b11 junction: prefix + new children + old children.
        let region: rsmt_core::Key = [1, 2, 3, 4, 5, 6, 7, 8, 9];
        let pre = node_prefix_io(&perm, 7, &region);
        let l = rsmt_hash::digest_of(&pre.output);
        let r = l;
        let newc = node_children_io(&perm, &pre.output, &l, &r);
        let oldc = node_children_io(&perm, &pre.output, &l, &r);
        let j = plan.record_join(pre, newc, Some(oldc));
        assert_eq!(j.prefix, 2); // ff: [leaf0, leaf1, prefix]
        assert_eq!(j.new_children, 1);
        assert_eq!(j.old_children, Some(2));

        // One opening: prefix + node.
        let opre = node_prefix_io(&perm, 3, &region);
        let node = node_children_io(&perm, &opre.output, &l, &r);
        plan.record_open(opre, node);

        // n_leaf=1, n_join=1, n_open=1, n_b11=1.
        plan.verify_counts(1, 1, 1, 1).expect("counts hold");
        assert_eq!(plan.n_ff(), 4); // 2·n_leaf + n_join + n_open
        assert_eq!(plan.n_term(), 4); // n_leaf + n_join + n_b11 + n_open
        assert_eq!(plan.n_perm(), 8); // 3·n_leaf + 2·n_join + n_b11 + 2·n_open

        // Table-B order is ff segment then terminal segment.
        assert_eq!(plan.table_b_order().count(), 8);
    }

    #[test]
    fn verify_counts_rejects_mismatch() {
        let mut plan = PermutationPlan::new();
        plan.push_ff(zero_io());
        // Claims a leaf (needs 2 ff + 1 term) but only 1 ff / 0 term recorded.
        assert!(plan.verify_counts(1, 0, 0, 0).is_err());
    }

    #[test]
    fn non_b11_join_records_no_old_children() {
        let perm = default_perm();
        let mut plan = PermutationPlan::new();
        let region9: rsmt_core::Key = [9, 8, 7, 6, 5, 4, 3, 2, 1];
        let pre = node_prefix_io(&perm, 5, &region9);
        let d = rsmt_hash::digest_of(&pre.output);
        let newc = node_children_io(&perm, &pre.output, &d, &d);
        let j = plan.record_join(pre, newc, None);
        assert_eq!(j.old_children, None);
        plan.verify_counts(0, 1, 0, 0).expect("b00/b01/b10 join");
        assert_eq!(plan.n_term(), 1); // only the new children block
    }
}
