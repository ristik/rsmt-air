# RSMT append-only theorem and the new-leaf ordering lemma (M0)

`DEVPLAN-R3.md` M0 deliverable ④, and the enabling argument for eliminating the
batch table (§2.2). Two results:

- **Theorem A (append-only).** An accepting consistency stream witnesses a
  non-destructive insertion: `new_root` is the root of the old tree with a set of
  fresh leaves added, and every pre-existing leaf is preserved.
- **Lemma B (new-leaf ordering).** In any accepting stream the keys of the `L`
  opcodes, read in stream order, are strictly increasing; hence the extracted
  batch is exactly that ordered subsequence, and no separate sorted-batch input is
  needed.

Notation from `crates/rsmt-core`: keys are 256-bit MSB-first; `key_bit(k, d)` is
the bit at absolute depth `d` (0 = most significant); `region_limbs(k, d)` is the
`d`-bit prefix; a junction `N(d)` bifurcates at depth `d`.

## Lemma B — new-leaf ordering

**Claim.** Let `Π` be a stream accepted by `V_RSMT`. Let `k_1, k_2, …, k_t` be the
keys attached to the `L` opcodes in the order the opcodes appear in `Π`. Then
`k_1 < k_2 < … < k_t` (as 256-bit unsigned integers), and this sequence equals the
batch consumed by `V_RSMT`.

**Proof.**

*Sub-tree key ranges.* Consider any junction `N(d)` accepted in `Π`, with left
child subtree `T_L` and right child subtree `T_R` (the two stack entries it pops,
in post-order the left was pushed first). By the coherence check, both advised
children share the prefix `p = region_limbs(rho, d)` on bits `[0, d)`, the left
child has `key_bit(·, d) = 0` and the right child has `key_bit(·, d) = 1`
(`SideMismatch` otherwise), and every leaf below an advised child extends that
child's region (edges only descend, `delta > d`, `CoherenceDepth` otherwise).
Therefore **every** key appearing in `T_L` agrees with `p` on `[0, d)` and has bit
`d = 0`, and every key in `T_R` agrees with `p` on `[0, d)` and has bit `d = 1`.
Because bit `d` is more significant than all bits below it and the two ranges
share bits above `d`, every key in `T_L` is strictly less than every key in `T_R`.

*Post-order = in-order on keys.* The stream is post-order: `T_L` is emitted in
full, then `T_R`, then `N(d)`. Restricting to `L` opcodes and applying the range
fact inductively over the tree, the `L` keys are emitted in increasing key order,
so `k_1 < k_2 < … < k_t`.

*Distinctness.* Two equal keys `k = k'` would have to sit in the same tree; at
their lowest common junction `N(d*)` one lands in `T_L` (bit `d* = 0`) and the
other in `T_R` (bit `d* = 1`), contradicting `k = k'`. So the inequalities are
strict.

*Batch identity.* `V_RSMT` consumes `L` operands from the batch in stream order
and independently rejects any batch that is not strictly increasing
(`BatchNotSorted`) and any leftover (`LeftoverBatch`). Hence the consumed batch is
exactly `k_1 < … < k_t`. ∎

**Consequence for R3.** The extracted batch is precisely the `L` subsequence in
op-row order; its sortedness is a *theorem from topology + coherence*, not a
trusted property of the witness builder. R3 therefore extracts the batch from the
`L` rows and drops the batch table (former Table D). The witness builder may still
sort for convenience, but sorting is never trusted verifier preprocessing. This is
soundness lemma **S2** in code/test form.

> **Obligation.** Lemma B must be tested *differentially*: a builder that emits
> `L` keys out of order, or with a duplicate, must fail plan construction and/or
> proof verification. If some arithmetization cannot enforce the range fact from
> topology alone, a narrow explicit order argument must be restored — sorting must
> not be re-admitted as trusted input.

## Theorem A — append-only insertion

**Claim.** Suppose `V_RSMT` accepts `(Π, old_root, new_root, batch)` with `batch`
the ordered `L` keys of Lemma B. Let `T_old` be the tree whose root is `old_root`
(under the authenticated-root assumption). Then:

1. `new_root` is the root of `T_new := insert_all(T_old, batch)`, the path-
   compressed RSMT obtained by inserting each `(key, value) ∈ batch`; and
2. every leaf of `T_old` is a leaf of `T_new` with an unchanged value (append-only
   / non-destructive): the transition adds leaves and refines internal structure
   but never removes or mutates an existing leaf.

**Proof sketch (and how it is discharged).** The proof is by structural induction
on `Π` matching the recursion of `Tree::insert`/`_build`/`_emit_preserved`
(`crates/rsmt-core/src/tree.rs`), which is the reference implementation of
`insert_all`:

- `S(h)` re-presents a preserved subtree whose old and new digests coincide (`h`);
  it contributes an unchanged subtree to both `T_old` and `T_new` — the append-only
  invariant holds trivially and no batch key falls inside it (else an opening,
  not `S`, would be required by coherence at the enclosing junction).
- `O(d, region, c_l, c_r)` opens one preserved junction level; both its children
  carry equal old/new digests unless a descendant `L` refines them, and the region
  is canonical for `d`. It preserves the enclosing structure of `T_old`.
- `OL(key, value)` re-presents a preserved leaf unchanged (old digest = new
  digest = `hash_leaf(key, value)`).
- `L` introduces a fresh leaf (`old = None`), so it can only *add*.
- `N(d)` combines children by the four-way old-state rule: the old digest is a
  passthrough or a re-hash of *old* child digests, so the old side of the junction
  reconstructs exactly `T_old`'s subtree; the new side always re-hashes the new
  child digests, so it reconstructs the inserted subtree. Confinement (both
  children advised at a *new* junction) is exactly the condition under which a new
  bifurcation is created by inserting a key that diverges from an existing leaf.

At the root, the old side reconstructs `old_root` (clause 5 of `R_R3`) and the new
side reconstructs `new_root`; because every old-side computation is a passthrough
or re-hash of *old* digests, `T_old`'s leaves survive unchanged (clause 2), while
the only `None`→`Some` transitions are introduced by `L` (clause 1).

**Discharge.** Rather than re-derive `insert_all` on paper, R3 relies on the
*differential oracle*: `crates/rsmt-core` runs `verify_consistency` against
`Tree::insert` over the cross-language vector corpus (`tests/differential.rs`,
byte-identical vs `rsmt6a.py` over ~10² rounds) plus shadow-insertion /
re-record / tamper-rejection tests. Theorem A is thus **cited** for R3 with the
reference `Tree` as its model, and the append-only invariant is the property those
tests exercise. Any change to `tree.rs`/`proof.rs` re-opens this obligation.

## Relationship to the security theorems

Theorem A + Lemma B live at the **RSMT-model** layer (they are about the abstract
`V_RSMT` and the reference tree). The **algebraic theorem** (S12) shows accepted
traces extract to an accepting `V_RSMT` execution; composing it with Theorem A
gives the **system theorem**: an accepted R3 proof (under Poseidon2 collision
resistance and authenticated `old_root`) witnesses a non-destructive insertion
from the authenticated old tree to `new_root`.
