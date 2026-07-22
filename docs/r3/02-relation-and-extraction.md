# The abstract R3 relation and extraction vocabulary (frozen, M0)

`DEVPLAN-R3.md` M0 deliverable ②. This defines `R_R3(public, witness)` and the
extraction map **without reference to any table name**, so the M4–M7
arithmetization and the M8 extraction theorem (S12) target a fixed relation.

Symbols follow `crates/rsmt-core`: `KEY_BITS = 256`, keys/values are 32-byte
strings, `Encode32` maps 32 bytes to the nine MSB-first BabyBear limbs of widths
`(30×8, 16)`, and `V_RSMT` is the abstract consistency verifier implemented by
`verify_consistency` (`proof.rs`), the differential oracle.

## 1. Objects

```text
Key32   := [u8; 32]                 canonical, exactly 32 bytes
Value32 := [u8; 32]                 canonical, exactly 32 bytes
Digest  := [BabyBear; 8]            a Poseidon2 node/leaf digest
Region  := 9 MSB-first limbs        left-aligned d-bit prefix, zero below d
Depth   := integer in [0, 256]
```

`Encode32 : {0,1}^256 → Region` is injective by construction (fixed limb widths,
each digit range-checked); `Decode32` is its partial inverse on canonical limbs.

## 2. Reference execution

An **abstract execution** is a sequence of opcodes

```text
op ∈ { S(h) , O(d, region, c_l, c_r) , OL(key, value) , L , N(d) }
```

together with, for `L`, the consumed `(key, value)` pair. `V_RSMT` runs a stack
machine (`proof.rs`) whose entries are `(old_digest?, new_digest, advice)` with
`advice ∈ {⊥} ∪ (Depth × Region)`, and enforces, in order:

- **depth range** `d < 256` for `O` and `N`;
- **region canonicality** `is_canonical_region(region, d)` for `O`;
- **leaf hashing** `hash_leaf(key, value)` for `L`/`OL`;
- **coherence** at each `N(d)`: every advised child has `delta > d` and region bit
  `d` equal to its side (0 = left, 1 = right); advised children agree on the
  prefix `region_limbs(rho, d)`; at least one child is advised;
- **confinement**: a *new* junction (some child has `old_digest = None`) requires
  **both** children advised;
- **four-way old state**:
  `(None,None)→None`, `(None,Some r)→r`, `(Some l,None)→l`,
  `(Some l,Some r)→hash_node(d, p, l, r)`;
- **new state** always `hash_node(d, p, new_l, new_r)`;
- **termination**: stack size 1, batch fully consumed, final `(old, new)` equals
  the claimed `(old_root, new_root)`.

## 3. The relation

Let `public = (protocol_id, old_root_is_none, old_root, new_root, shape)`.

`R_R3(public, witness) = 1` **iff** all hold:

1. **Protocol match** — `protocol_id` names the fixed R3 AIR set, Poseidon2
   constants, field, extension, PCS, transcript, and FRI parameters.
2. **Shape consistency** — `shape` (scalar counts only) is consistent with the
   trace domains and the fixed preprocessing, and satisfies the count identities
   and per-bus no-wrap bounds of `04-soundness-budget.md`.
3. **Well-formed decode** — the witness decodes to a well-formed opcode execution
   with **exact** 32-byte keys and values (`Encode32`) and **canonical** opened
   regions.
4. **Reference acceptance** — that execution satisfies the RSMT digest algebra,
   coherence, confinement, and post-order rules of §2.
5. **Boundary** — its final stack item is exactly the public old/new root pair,
   including the `None` vs `Some([0;8])` distinction:
   `old_root_is_none = 1 ⇒ old side is None`;
   `old_root_is_none = 0 ⇒ old side = old_root` (which may be `[0;8]`).

**Existential-batch scope.** The batch is *existential* in the public statement:
`R_R3` asserts "there exists a set of canonical 32-byte leaves producing this
transition," not "this externally supplied list was applied." This matches the
public-root-only API. Attesting a *particular* hidden batch requires a public
batch commitment and an in-AIR binding to it — a distinct, versioned extension,
not assumed here (`DEVPLAN-R3.md` §2.2).

## 4. Extraction vocabulary (for the S12 theorem)

The M8 extraction theorem must define a deterministic map from **real** trace rows
to an abstract execution, using only these observable quantities (named
abstractly; each maps to concrete columns/buses per milestone):

| Extracted item | Source obligation | Lemma |
|---|---|---|
| opcode of each real op-row | exactly one selector set, none on padding | S1 |
| post-order edges (parent, left, right) | contiguous `subtree_start` chain + in-degree-1 tree bus | S2 |
| child digest ↔ advice pairing | one tuple carries digest+None+depth+region+start, keyed by unique row index | S3 |
| `(key, value)` of each `L`/`OL` | injective limb reconstruction from range-checked digits | S4 |
| opened `region` of each `O` | canonical digit reconstruction + boundary/zero-suffix | S5 |
| coherence prefix `p`, side bits, gap | R10-bounded integer equations at each `N` | S6 |
| four-way old digest | child `None` bits select the case; shared prefix used old+new | S7 |
| each Poseidon2 evaluation | one send / one receive per logical occurrence | S8 |
| range/power facts | fixed-table balance, no multiplicity wrap | S9 |
| `old_root`, `new_root`, `old_root_is_none` | last real row public boundary | S1, S12 |

The extraction **may quotient away class-6 irrelevant cells** (`01`-§7); it must
**not** assume they are uniquely constrained. The theorem's conclusion is exactly
clause 4–5 of §3: the extracted execution is accepted by `V_RSMT` and its roots
equal the public roots.

## 5. What extraction does *not* provide

- It does not certify which real-world batch was applied (existential scope).
- It does not establish that `old_root` is globally canonical (state chaining).
- It does not provide confidentiality of any extracted witness fragment (no ZK).

These are handled by the system theorem and integration layer, not by `R_R3`.
