# R3 security model (frozen, M0)

Derived from `DEVPLAN-R3.md` §§2–3. This is the authoritative statement of what
an accepted R3 proof means and does not mean. It is written so that a reviewer
can state the guarantee without reading any table code.

## 1. System and intended use

The Unicity Aggregator maintains a path-compressed sparse Merkle tree (RSMT). A
round starts from an authenticated old root and adds a finite set of fresh
`(key, value)` leaves, producing a new root. A compact consistency-proof stream
(opcodes `S / O / OL / L / N`, see `crates/rsmt-core/src/proof.rs`) opens only the
preserved structure needed to justify the additions. The STARK replaces native
execution of that stream for an external verifier.

The public state for one **non-empty** round is

```text
Statement = (protocol_id, old_root_is_none, old_root[8], new_root[8], shape)
```

where the roots are BabyBear digests and `shape` fixes every AIR height and every
deterministic preprocessed mask. Everything else — opcode stream, added leaves,
opened nodes/leaves, intermediate digests, coherence decompositions, Poseidon2
evaluations, lookup multiplicities — is **witness**. "Witness" means *not a public
input*; it does **not** mean confidential (see §5, non-goals).

The **empty** round is a separate non-STARK case (`IdentityTransition`): it accepts
only `old_root = Some(new_root)` with no opcode/batch witness. It must never
produce a zero-height AIR whose unconstrained boundary could certify arbitrary
roots (`DEVPLAN-R3.md` R3-D11).

## 2. Adversary

The adversary controls the prover and all witness data. It may:

- choose malformed opcodes, leaves, openings, trace values, padding values,
  multiplicities, and permutation requests;
- choose any allowed public shape and exploit power-of-two padding cliffs;
- submit malformed or non-canonical proof bytes;
- try to mix data between rows or tables;
- repeat equal Poseidon2 inputs;
- adapt the proof to the public roots and all prior public transcripts; and
- spend bounded computation grinding commitments or Fiat–Shamir challenges.

The adversary does **not** choose: the verifier implementation; `protocol_id`,
field, extension, Poseidon2 constants, transcript domain, FRI/PCS configuration,
or lookup definitions; verifier-owned preprocessing commitments; the accepted old
root in the surrounding state machine; or the random-oracle / primitive internals
except through their specified interfaces.

## 3. Required security property

**Primary property — computational soundness.**

> For every PPT prover, the probability that the R3 verifier accepts
> `(public, proof)` while no canonical witness satisfies `R_R3(public, witness)`
> (see `02-relation-and-extraction.md`) is negligible in the configured security
> level.

At the arithmetization layer this decomposes into five obligations:

1. **AIR faithfulness** — satisfying traces extract to an accepting abstract RSMT
   execution.
2. **LogUp soundness** — a false cross-table multiset equality is accepted only
   with the bounded challenge-collision probability.
3. **STARK soundness** — committed traces are low-degree and satisfy the AIR
   except with the configured FRI/Fiat–Shamir error.
4. **Encoding faithfulness** — extracted keys, values, regions, public fields,
   shapes, and proof elements have exactly one accepted external encoding.
5. **Hash binding** — at the tree-semantics layer, two different canonical objects
   cannot feasibly be substituted under one Poseidon2 digest.

The repository states two theorems separately:

- an **algebraic theorem**, conditional on the STARK and LogUp arguments, that
  accepted traces extract to `V_RSMT`; and
- a **system theorem**, additionally conditional on Poseidon2 collision resistance
  and authenticated root chaining, that accepted roots have the intended tree
  meaning.

This separation avoids claiming collision resistance is needed to prove an
in-circuit permutation was evaluated, while still recording where it is needed to
interpret a digest as a unique tree object.

## 4. Completeness

For every non-empty transition accepted by the abstract verifier over canonical
`Key32`/`Value32` leaves, the witness builder must produce traces of an allowed
shape satisfying all local constraints and buses. Honest transitions must **not**
fail because of: duplicated Poseidon2 inputs; padding boundaries; an opening at
depth `0`, `239`, `240`, or `255`; `None` vs a present all-zero digest; a
one-child old-state passthrough; equal old/new terminal permutation inputs in
different logical places; or a valid distribution of `S/O/OL/L/N` rows.

Completeness is the explicit reason global permutation deduplication is removed:
two logical receives require multiplicity two even when their tuples are equal
(`DEVPLAN-R3.md` R3-D7).

## 5. Stateful interpretation, assumptions, non-goals

**Stateful interpretation.** A proof alone does not establish that `old_root` is
the globally accepted state. The system theorem is inductive: (1) a genesis rule
or trusted checkpoint authenticates `root_0`; (2) each accepted R3 proof
establishes a valid transition `root_i → root_{i+1}`; (3) the consensus layer
prevents competing successors from being treated as the same canonical round. A
verifier that accepts an attacker-chosen old root with no chain proves only a
valid transition *from that attacker-chosen tree* — this must be explicit in the
integration docs, not an AIR change.

**Assumptions.** Pinned Plonky3 batch-STARK / Poseidon2-AIR / PCS / challenger /
LogUp behave as specified; BabyBear degree and two-adicity limits are enforced;
extension field and #challenges meet the derived error bound
(`04-soundness-budget.md`); fixed Poseidon2 instances give the claimed
collision/preimage resistance; the verifier obtains the old root from an
authenticated chain; the proof decoder and resource limits run before allocation.

**Non-goals.** Zero knowledge / witness indistinguishability; transaction
authorization or payload validity; consensus over which valid successor wins;
attestation of a *particular* batch without a public batch commitment; variable-
length values; PQ claims beyond those justified for the chosen hashes; backward
verification of pre-R3 proof bytes.

The model deliberately relaxes exactly three things not needed by the application:
arbitrary-length leaf values; zero knowledge; and unique determination of
semantically irrelevant witness cells (§7). It does **not** relax canonical key
placement, confinement, hash evaluation, public-root binding, post-order
topology, lookup balance, or verifier ownership of the statement and parameters.

## 6. Canonical encoding

Canonicality is required wherever an external byte object is claimed:

- key: exactly 32 bytes;
- value: exactly 32 bytes;
- opened region: exactly the `d`-bit prefix, left-aligned and zero below `d`;
- public BabyBear element: integer in `[0, p)`, encoded once;
- `old_root_is_none`: one byte / field boolean with only `0` and `1`;
- shape integer: a minimally encoded bounded unsigned integer;
- proof envelope: one protocol version, no trailing or duplicate fields.

Canonicality is **not** required for an internal algebraic helper with no external
byte semantics, provided its range/relations suffice for the soundness proof.

## 7. Influence classification (replaces "every cell constrained")

"Every main cell changes a constraint when incremented" is a bug-finding
heuristic, not the theorem: a Table-R multiplicity is locally free but globally
fixed by LogUp balance, while a constrained column can still be insecure if bound
to the wrong bus tuple. Classify every witness column into exactly one of:

1. **statement-bearing** — reaches a public boundary;
2. **execution-bearing** — determines an extracted opcode, digest, advice, key,
   value, region, or topology edge;
3. **cryptographic** — a Poseidon2 input/output or continuation state;
4. **interaction-bearing** — appears in a lookup element or multiplicity;
5. **algebraic helper** — exists only to keep constraints low-degree and is
   functionally related to 1–4; or
6. **irrelevant** — changing it cannot affect classes 1–5 or satisfiability.

Classes 1–5 need a documented local, boundary, or bus relation. Class 6 does not
weaken semantic soundness but should normally be deleted; if it must remain for a
generic upstream layout, put it on a reviewed noninterference allowlist and prove
it never enters an expression, lookup, public output, or extracted execution
(enforced by the M8 influence manifest). Padding is different: padding values and
multiplicities must be constrained or masked wherever they could enter an AIR or
bus.
