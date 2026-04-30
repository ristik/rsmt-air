# Plonky3 AIR for RSMT3 Consistency Proofs

This document specifies the AIR layout, constraints, and lookup buses used by
the `rsmt-air` workspace to prove correctness of a sorted batch of insertions
into the RSMT3 sparse Merkle tree, instantiated over BabyBear + Poseidon2.

The proof binds two public digests — `old_root[8]` and `new_root[8]` — and
nothing else. The batch and the consistency proof itself are private inputs;
the verifier accepts the proof on the basis of public roots alone.

## 1. Hash specification

BabyBear, Poseidon2 width 16, digest width 8. Domain tags
`DOMAIN_LEAF = 1`, `DOMAIN_NODE = 2`. 256-bit keys / 32-byte values pack as
9 × 30-bit BabyBear limbs (limbs `0..7` carry 30 bits, limb `8` carries 16).

**Node hash.**

```
state = [left[0..8] || right[0..8]]
state[0] += DOMAIN_NODE
state[1] += depth
state' = Poseidon2(state)
digest = state'[0..8]
```

The bottom 8 elements `state'[8..16]` (the node-hash *tail*) are dropped from
the digest but are still needed in-circuit so that Bus 2 can carry the full
`(input[16] || output[16])` tuple of every Poseidon2 evaluation.

**Leaf hash (additive sponge, 3 absorb steps, rate 8 / capacity 8).**

Each step adds new rate inputs into the *full* previous output (rate +
capacity carry through unchanged across the permutation):

```
state ← [0; 16]

# step 0:
state[0] += DOMAIN_LEAF
for j in 0..7: state[1+j] += key[j]
state ← Poseidon2(state)

# step 1:
state[0] += key[7]
state[1] += key[8]
for j in 0..6: state[2+j] += value[j]
state ← Poseidon2(state)

# step 2:
state[0] += value[6]
state[1] += value[7]
state[2] += value[8]
state ← Poseidon2(state)

leaf_digest = state[0..8]
```

> **Additive vs overwrite.** The reference implementation (`rsmt-hash`) uses
> additive mode: the previous full state is carried into the next permutation
> input and the new rate inputs are added to it. Table C's per-step input
> expression therefore reads `state_in[j] = state_prev[j] +
> rate_pattern(step, key, value)[j]` for `j ∈ [0,16)`, where
> `rate_pattern[step]` is zero on capacity slots `j ∈ [8,16)`.

## 2. Tables

The proof uses six AIRs (`A, F, B, C, D, E`) sharing one main commitment via
`p3-batch-stark`. Each AIR is padded independently to a power of two ≥ 2.
A single enum `RsmtAir { A, F, B, C, D, E }` dispatches the trait
implementations so `prove_batch` (which requires a single concrete AIR type)
can carry all six.

### Table A — Verification rows (one per opcode)

Trace height = `next_pow2(P)` where `P` is the total number of opcodes in
the proof.

**Preprocessed (3 columns)**: `row_idx`, `is_real`, `is_last_real`.
Padding is at the end, so the first real row is row 0 and `is_last_real`
fires on the last opcode in the consistency proof.

**Witness (24 columns)**:

| Cols | Width | Purpose |
|---|---:|---|
| `is_s, is_l, is_n` | 3 | one-hot opcode selector |
| `depth` | 1 | range-checked via Bus 5; only meaningful on `N` rows |
| `batch_idx` | 1 | index into the sorted batch on `L` rows |
| `old_hash[8]` | 8 | pre-state digest (zero if `old_is_none = 1`) |
| `new_hash[8]` | 8 | post-state digest |
| `old_is_none` | 1 | bool |
| `left_ptr` | 1 | left-child row index for `N` rows |
| `node_hash_old_needed` | 1 | bool, equal to `b11` from Table F on `N` rows |
| **Total** | **24** | |

**Local constraints** (all multiplied by `is_real`):

- booleanity: `is_s, is_l, is_n, old_is_none, node_hash_old_needed ∈ {0,1}`;
- one-hot: `is_s + is_l + is_n = 1`;
- `is_l * (1 - old_is_none) = 0` (L → none);
- `is_s * old_is_none = 0` (S → not none);
- `is_s * (old_hash[j] - new_hash[j]) = 0` for `j = 0..7`;
- `is_l * old_hash[j] = 0` for `j = 0..7`;
- `is_l * left_ptr = is_l * depth = is_l * node_hash_old_needed = 0`;
- `is_s * left_ptr = is_s * depth = is_s * batch_idx = is_s * node_hash_old_needed = 0`;
- `is_n * batch_idx = 0`;
- canonical zeroing: `old_is_none * old_hash[j] = 0` for `j = 0..7`;
- padding-row syntactic zero: `(1 - is_real) * column[j] = 0` for every
  witness column `j`.

**Boundary** (gated by `is_last_real`):

- `is_last_real * (old_hash[j] - public_old_root[j]) = 0`,
- `is_last_real * (new_hash[j] - public_new_root[j]) = 0`.

There is **no** `is_last_real * old_is_none = 0` constraint — that would
break empty-pre-state batches, where the genuine pre-root is the
canonically-zero "none" digest. The boundary equality with `public_old_root`
already pins the canonical encoding.

**Public values**: `[old_root[0..8], new_root[0..8]]` (16 elements).

### Table F — N-Join (one row per `N` op)

Trace height = `next_pow2(N_op)`. This table holds left/right child digests
for each `N` row of Table A so that the four-way old-hash rule can be
expressed with local constraints.

**Preprocessed (1 column)**: `is_real_f`.

**Witness (74 columns)**:

| Cols | Width | Purpose |
|---|---:|---|
| `parent_row_idx, left_ptr, right_ptr, depth` | 4 | indices and depth |
| `left_old[8], left_new[8], left_none` | 17 | left child tuple |
| `right_old[8], right_new[8], right_none` | 17 | right child tuple |
| `parent_old[8], parent_new[8], parent_none` | 17 | parent tuple |
| `b01, b10, b11` | 3 | derived selectors |
| `parent_old_tail[8], parent_new_tail[8]` | 16 | bottom-8 outputs of node-hash Poseidon2 |
| **Total** | **74** | |

`b00 = parent_none = left_none * right_none` is implicit; the three
selectors `b01, b10, b11` are explicit so the four-way rule stays
low-degree.

**Constraints** (all multiplied by `is_real_f`):

- booleanity of `left_none, right_none, parent_none, b01, b10, b11`;
- `parent_row_idx - right_ptr - 1 = 0`;
- `b01 = left_none * (1 - right_none)`;
- `b10 = (1 - left_none) * right_none`;
- `b11 = (1 - left_none) * (1 - right_none)`;
- `parent_none = left_none * right_none`;
- four-way passthrough, componentwise for `j = 0..7`:
  `(1 - b11) * parent_old[j] = b01 * right_old[j] + b10 * left_old[j]`;
- canonical zeroing: `parent_none * parent_old[j] = 0` for `j = 0..7`;
- tail canonical zeroing: `(1 - b11) * parent_old_tail[j] = 0` for
  `j = 0..7` (passthrough rows do not send Bus 2 old-hash, so the tail must
  not carry smuggled values);
- padding-row syntactic zero: `(1 - is_real_f) * column[j] = 0` for every
  witness column.

`parent_new = H_node(left_new, right_new, depth)` and (when `b11 = 1`)
`parent_old = H_node(left_old, right_old, depth)` are enforced through
Bus 2; see §3.

The locality `right_ptr = parent_row_idx - 1`, combined with the multiset
equality on Bus 1 (each non-root real Table-A row is consumed exactly once
as a child by some Table F row), reproduces the post-order tree shape.

### Table B — Poseidon2 permutation

Built directly from `p3-poseidon2-air::VectorizedPoseidon2Air` with
`WIDTH=16, SBOX_DEGREE=7, SBOX_REGISTERS=1, HALF_FULL_ROUNDS=4,
PARTIAL_ROUNDS=13, VECTOR_LEN=8`. The main trace is the unmodified
vectorized layout; the AIR's inner constraints check that each lane is a
real Poseidon2 evaluation.

**Trace height** = `next_pow2(ceil(num_perms / 8))` where `num_perms` =
`#L · 3 + #N + #N_old_needed` (one permutation per leaf-sponge step plus
one per junction-new and per junction-old as gated by `b11`).

**Preprocessed**: `P2_VECTOR_LEN = 8` columns of per-lane real/pad masks.
The mask lives in preprocessed (not main) because adding a column to the
main width would break `Poseidon2Air::eval`'s `borrow::<Poseidon2Cols>()`
length assertion.

**Padding lanes are real Poseidon2 evaluations of `[0; 16]`** — the inner
constraints must hold on every row; the lane-mask only zeros the Bus 2
Send multiplicity for padded lanes.

Table B sends, per lane, on Bus 2 (`p2`) at multiplicity `is_real_lane[lane]`:

```
elements = (input[0..16] || post[0..16])    # 32 BabyBear elements
direction = Send
```

rsmt-air registers each tuple with its own `Lookup` (and aux column set),
so Table B emits **eight separate `Lookup`s** (one per lane). The
`register_lookup` API also accepts multi-input lookups that share aux
columns, but the per-tuple form is what this design uses.

### Table C — Leaf sponge controller (3 rows per `L` op)

Trace height = `next_pow2(3 · B)` where `B` is the number of leaves in the
batch.

**Preprocessed (5 columns)**: `leaf_idx`, `is_step_0`, `is_step_1`,
`is_step_2`, `is_real_c`.

The layout `[0,0,0,1,1,1,2,2,2,…]` for `leaf_idx` and the cyclic
`[is_step_0, is_step_1, is_step_2]` indicators are fixed once `B` is known,
so they are materialized as preprocessed columns. This makes the multiset
of `leaf_idx` exactly `{0..B−1}`, with each value receiving exactly one
final-step (`is_step_2`) row — no witness counter or extra bus is needed
to enforce uniqueness.

**Witness (50 columns)**: `key[9] | value[9] | state_in[16] | state_out[16]`.

**Local constraints** (gated by `is_real_c`):

- padding zero: `(1 - is_real_c) * column[j] = 0` for every witness column;
- step-0 initialization (gated by `is_step_0`):
  - `state_in[0] = DOMAIN_LEAF`;
  - `state_in[1+j] = key[j]` for `j = 0..6`;
  - `state_in[8..16] = 0`;
- transitions into step 1 / step 2 (gated by `is_step_1_next` /
  `is_step_2_next` from the preprocessed columns of the next row): for
  each `j ∈ [0,16)`,
  `next.state_in[j] = local.state_out[j] + inj_step{1,2}[j]`,
  where the injection patterns are
  - step-1 injection: `[k7, k8, v0..v5, 0, 0, 0, 0, 0, 0, 0, 0]`,
  - step-2 injection: `[v6, v7, v8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]`;
- key/value continuity within one leaf: when the next row is step 1 or
  step 2, `next.key = local.key` and `next.value = local.value`.

`state_out` is committed in full (all 16 columns); Bus 2 receives
`(state_in[0..16] || state_out[0..16])` per real row, and Bus 4 sends only
`state_out[0..8]` (the digest) on the last step.

### Table D — Sorted batch (preprocessed-only)

Trace height = `next_pow2(B)`. Width: `1` dummy main column (the batch
data lives entirely in preprocessed; Plonky3 batch-STARK still requires a
non-empty main trace per instance).

**Preprocessed (20 columns)**: `idx, is_real_d, key[9], value[9]`.

Batch sorting and 30-bit-limb packing is done by the prover before the
preprocessed trace is materialized; the 30-bit discipline is then
inherited by construction (no in-circuit bit decomposition).

The batch is **a private input**. The verifier never receives the batch
or its commitment as preprocessed-key material: `TableDAir::shape_only(h)`
constructs the verifier-side AIR with only the padded height, and the
prover's preprocessed commitment is observed through the batch-STARK
transcript and bound to public roots through the bus chain
`Bus 6 → Table C step 2 → Bus 4 → Table A L row → root`. The
soundness chain ties the prover's chosen batch to the public root
transition without exposing the batch.

### Table E — `u8` range check

Fixed 256 rows. **Preprocessed (1 column)**: `byte ∈ {0..255}`.
**Witness (1 column)**: `mult` — per-byte send multiplicity on Bus 5.

`mult` is pure witness, unconstrained locally. The witness builder sets
`mult[b]` to the count of N rows in Table A whose `depth = b`; LogUp's
multiset balance on Bus 5 enforces correctness. Constant `mult = 1` would
not balance in general because the number of N rows ≠ 256.

## 3. LogUp buses

Plonky3 LogUp (`p3-lookup::logup::LogUpGadget`) uses one extension-field
auxiliary column per bus. Per-bus challenges `(α, β)` are sampled after the
main commitment. All buses are global (`Kind::Global(name)`); the verifier
checks `Σ expected_cumulated = 0` per bus name across all AIRs.

| # | Name | Tuple | Sender | Receiver |
|---|---|---|---|---|
| 1 | `tree` | `(row_idx, old_hash[8], new_hash[8], old_is_none)` (18 elts) | Table A real non-last rows, mult `is_real * (1 - is_last_real)` | Table F: 1× via `(left_ptr, left_old, left_new, left_none)` and 1× via `(right_ptr, right_old, right_new, right_none)`, each at mult `is_real_f` |
| 2 | `p2` | `(in[0..16], out[0..16])` (32 elts) | Table B per packed lane, mult `is_real_lane[lane]` | Table F new-hash mult `is_real_f`; Table F old-hash mult `is_real_f * b11`; Table C per real row mult `is_real_c` |
| 3 | `parent` | `(parent_row_idx, parent_old[8], parent_new[8], parent_none, depth, node_hash_old_needed)` (20 elts) | Table F, mult `is_real_f` | Table A N rows, mult `is_real * is_n` |
| 4 | `leaf_hash` | `(batch_idx, digest[0..8])` (9 elts) | Table C step 2, mult `is_step_2` | Table A L rows, mult `is_real * is_l` |
| 5 | `u8` | `(byte)` | Table E, mult `mult` (witness column) | Table A N rows, mult `is_real * is_n` (key = `depth`) |
| 6 | `batch` | `(idx, key[0..9], value[0..9])` (19 elts) | Table D, mult `is_real_d` | Table C step 2, mult `is_step_2` |

Bus 2's tuple is the full Poseidon2 input‖output (32 elements). Both
junction-hash receives constructed by Table F use that shape:

- new-hash receive (always when `is_real_f`):
  `(left_new[0..8] | with [0] += DOMAIN_NODE, [1] += depth)
  || right_new[0..8]
  || parent_new[0..8]
  || parent_new_tail[0..8]`
  at multiplicity `is_real_f`.
- old-hash receive (only when `b11 = 1`):
  same shape using `_old` digests and `parent_old_tail`,
  at multiplicity `is_real_f * b11`.

Storing `parent_*_tail[8]` on Table F is what makes the single-bus design
work: the bus tuple matches Table B's send exactly. Without the tail, the
bottom-8 outputs would be unconstrained and a malicious prover could
submit non-Poseidon2 values matching only the truncated digest.

### Why this set is sufficient

- **Bus 1** forces every non-root, non-padding Table A row to be consumed
  exactly once as a child by some Table F row. Combined with
  `right_ptr = parent_row_idx − 1` in Table F, this is the post-order
  tree shape.
- **Bus 3** binds each Table A `N` row to exactly one Table F row;
  without it, Table F rows could be silently fabricated.
- **Bus 2** forces every requested node hash (new always, old conditionally)
  and every leaf-sponge step to be a real Poseidon2 evaluation.
- **Bus 4** + **Bus 6** together force every L row to consume one
  final-step digest, and every final step to consume one batch row. The
  L row's `batch_idx` is therefore equal to Table D's `idx` of the
  unique row consumed.
- **Bus 5** range-checks `depth ∈ {0..255}`.

## 4. Trace heights and padding

| AIR | Real rows | Padded height |
|---|---|---|
| A | `P` | `next_pow2(P)` |
| F | `N_op` | `next_pow2(N_op)` |
| B | `ceil((3B + N_op + N_op_old) / 8)` | `next_pow2(...)` |
| C | `3B` | `next_pow2(3B)` |
| D | `B` | `next_pow2(B)` |
| E | `256` | `256` |

All heights are independently rounded up to a power of two ≥ 2.
`prove_batch` commits the six main traces in a single
`TwoAdicFriPcs` commitment, samples per-bus `(α, β)`, builds the six
per-AIR LogUp aux traces in parallel, commits them in one extension-field
commitment, samples constraint-batching `α_c`, computes per-AIR quotient
values, commits quotient chunks, and runs FRI once over the batched
openings. Per-table padding cost is amortized by the shared FRI
commitment.

## 5. Plonky3 integration notes

The workspace pulls Plonky3 from `github.com/Plonky3/Plonky3` at a fixed
git rev (see `[workspace.dependencies]` in `Cargo.toml`). Crate version is
`0.5.x` at the pinned rev. Concrete API points an implementer must hit:

### `BaseAir` shape (Plonky3 ≥ 0.5)

- `BaseAir<F>: Sync` per AIR. `width()` returns the **witness** width;
  preprocessed columns are not counted there.
- `preprocessed_trace(&self) -> Option<RowMajorMatrix<F>>` returns the
  per-instance preprocessed trace, materialized once and committed
  separately. Its height must equal the trace's padded height (or trace
  height for non-zk).
- `main_next_row_columns(&self) -> Vec<usize>` and
  `preprocessed_next_row_columns(&self) -> Vec<usize>` declare which
  columns are read at row `i+1`. AIRs without transition constraints
  (Tables A, F, D, E) override both to `vec![]` so the prover and
  verifier do not open columns at `zeta_next`. Table C keeps the default
  (sponge transition reads the next row).
- `num_public_values(&self)` must match the slice passed to `prove*`.
- Trace height must be ≥ 2 (`log2_strict_usize` in
  `p3-uni-stark::prover.rs`).

### `WindowAccess` trait

`builder.main()` returns a `WindowAccess<AB::Var>` with `current_slice()`
and `next_slice()`. Use `current_slice` for purely-local constraints;
`next_slice()` (typically gated by `builder.is_transition()`) for
transitions.

### `LookupAir` extension trait

LogUp lookups are not part of `Air`. Each AIR additionally implements
`p3_lookup::LookupAir<F>` with three methods:

- `add_lookup_columns(&mut self) -> Vec<usize>`: allocate aux columns for
  one new lookup; return their indices into the auxiliary trace.
- `get_lookups(&mut self) -> Vec<Lookup<F>>`: enumerate every lookup this
  AIR participates in, expressed symbolically over a `SymbolicAirBuilder`
  of the AIR's main width. Each `Lookup` carries `(kind, element_exprs,
  multiplicities_exprs, columns)`.
- `register_lookup(&mut self, kind, &[lookup_inputs])`: convenience
  builder used inside `get_lookups`.

`Kind::Global(name.into())` makes the bus name-scoped and matched by value
across AIRs. rsmt-air registers **one `LookupInput` per `Lookup`**: for
multi-tuple AIRs (Table B's lanes, Table F's left/right children) we call
`register_lookup` once per tuple so each tuple gets its own aux column
set.

### Plonky3 HEAD batch-LogUp bug and workaround

At Plonky3 git rev `4b341cc9a19baf5f4e57164c10183acfeff6dd09`
(`Plonky3/Plonky3` main at the time of this integration), batch-STARK
verification fails for Table F if its two Bus 1 child receives are encoded
as **one** global `Lookup` containing two `LookupInput`s:

```rust
let tree_inputs = vec![
    (left_tuple, is_real_f.clone(), Direction::Receive),
    (right_tuple, is_real_f, Direction::Receive),
];
LookupAir::register_lookup(self, Kind::Global(BUS_TREE_NAME.to_string()), &tree_inputs);
```

The local AIR constraints and debug lookup balance checks pass, and proof
generation completes, but `verify_batch` rejects batch sizes ≥ 2 with:

```text
VerificationError::OodEvaluationMismatch { index: Some(1) }
```

`index: Some(1)` is Table F in the batch instance order. The same bus
semantics verify if the two child receives are registered as separate
global lookups with the same bus name:

```rust
let left_tree_lookup = LookupAir::register_lookup(
    self,
    Kind::Global(BUS_TREE_NAME.to_string()),
    &[(left_tuple, is_real_f.clone(), Direction::Receive)],
);
let right_tree_lookup = LookupAir::register_lookup(
    self,
    Kind::Global(BUS_TREE_NAME.to_string()),
    &[(right_tuple, is_real_f, Direction::Receive)],
);
```

This is the current workaround in `TableFAir::get_lookups`. It preserves
the `tree` bus accounting because Plonky3 sums `expected_cumulated` by
global bus name after per-instance verification; it only changes the
aux-column layout from one running-sum column covering both receives to
two running-sum columns, one per receive. Do not collapse Table F's
left/right child receives back into one multi-input `Lookup` unless the
upstream batch-LogUp verifier bug has been fixed and the full workspace
tests still pass.

### `prove_batch` and the heterogeneous-AIR dispatch

`p3_batch_stark::prove_batch<SC, A>` takes `&[StarkInstance<'_, SC, A>]`
where `A` is **a single concrete AIR type**. The six structurally
different AIRs are wired in via an enum-dispatch wrapper:

```rust
#[derive(Clone)]
enum RsmtAir {
    A(TableAAir),
    F(TableFAir),
    B(TableBAir),  // wraps VectorizedPoseidon2Air<...>
    C(TableCAir),
    D(TableDAir),
    E(TableEAir),
}
```

The wrapper implements `BaseAir<F>`, `Air<DebugConstraintBuilder<...>>`,
`Air<SymbolicAirBuilder<F, EF>>`, `Air<ProverConstraintFolderWithLookups<...>>`,
`LookupAir<F>`, and `Clone`. `add_lookup_columns` routes through a single
shared counter the wrapper owns.

### Batch as private input — verifier-side AIR construction

Table D's preprocessed trace embeds the batch. The **verifier** does not
have the batch and must not be given it. The verifier constructs Table D
via `TableDAir::shape_only(padded_height)`, which sets the `batch` field
to `None`. The prover-side AIR uses `TableDAir::for_batch(&sorted)` to
materialize the preprocessed trace once, during `ProverData::from_instances`.

The verifier's call path never invokes `BaseAir::preprocessed_trace()` —
it reads only `common.preprocessed` (the global preprocessed commitment)
and per-instance widths. `LookupAir::get_lookups()` references
preprocessed columns *symbolically* (by index), not by value. So the
verifier needs only:

1. The shape of each AIR (widths, padded heights, lookup wiring).
2. The global preprocessed commitment from `prover_data.common`.
3. The proof.
4. `[old_root, new_root]` as public values.

### Padding-row discipline

Tables A, F, C all enforce `(1 - is_real) * column[j] = 0` for every
witness column. This is the cheapest discipline that survives bus
integration; without it, selector-gated lookup arms can pick up nonzero
contributions on padding rows.

### Debug `check_constraints`

`p3_air::check_constraints(&air, &trace, &public_values)` runs every
constraint over every row using `DebugConstraintBuilder`. It does not
evaluate lookups (those need the LogUp aux trace built by the prover) but
catches local / boundary / transition violations immediately. Use it in
unit tests as the fastest path to per-AIR constraint debugging.

## 6. Concrete column counts

| AIR | Witness width | Preprocessed width |
|---|---:|---:|
| A | 24 | 3 |
| F | 74 | 1 |
| B (`VECTOR_LEN=8`) | `8 × P2_PERM_WIDTH` ≈ 2384 | 8 (lane mask) |
| C | 50 | 5 |
| D | 1 (dummy main) | 20 |
| E | 1 (`mult`) | 1 (`byte`) |

Aux trace adds one extension-field column per bus per AIR (six base-field
equivalents in BabyBear^4).

## 7. Measured performance

Fresh-batch workload (no prefill), release build:

| batch | L_ops | N_ops | B_perms | total cells | wit_ms | trace_ms | prove_ms | verify_ms | proof_KB |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16   | 16   | 15   | 63    | 25.6K | 0  | 0  | 30  | 41 | 1524 |
| 64   | 64   | 63   | 255   | 100K  | 0  | 0  | 23  | 38 | 1532 |
| 256  | 256  | 255  | 1023  | 401K  | 2  | 1  | 56  | 41 | 1605 |
| 1024 | 1024 | 1023 | 4095  | 1.6M  | 11 | 5  | 149 | 44 | 1693 |
| 4096 | 4096 | 4095 | 16383 | 6.4M  | 46 | 20 | 587 | 45 | 1760 |

Observations:

- Table B dominates (~76% of total cells across all batch sizes); Poseidon2
  row-layout optimization pays off proportionally.
- Verify time is essentially flat (~40 ms) — FRI overhead dominates and
  doesn't grow with batch size in this range.
- Proof size grows slowly with batch (1.5 → 1.8 MB across 256× scaling).
- Witness build (Poseidon2 three times per leaf) plus trace generation
  cost ~10% of prove time at batch = 4096.

## 8. Public inputs and verifier obligations

**Public inputs** (16 BabyBear elements):

```
[old_root[0..8], new_root[0..8]]
```

**Verifier obligations**:

1. Construct each AIR from shape only:
   - `TableAAir::new(padded_height_a, real_rows_a)`,
   - `TableFAir::new(padded_height_f, real_rows_f)`,
   - `TableBAir::new(padded_height_b, real_perms)`,
   - `TableCAir::new(padded_height_c, real_rows_c)`,
   - `TableDAir::shape_only(padded_height_d)`,    *(no batch data)*
   - `TableEAir::new()`.
2. Call `verify_batch(&config, &airs, &proof, &public_values, &common)`
   with `public_values[0] = [old_root, new_root]` for Table A and empty
   for the other AIRs. `common` is the per-proof `CommonData<SC>` that
   carries the global preprocessed commitment and the shared lookup wiring.
3. Confirm `LookupGadget::verify_global_final_value` returned `Ok` for
   each of the six bus names (this is folded into `verify_batch`'s return
   value).

The verifier never materializes the batch, the consistency proof, or any
preprocessed trace — only the per-instance padded heights and the
prover-supplied global preprocessed commitment are used.

## 9. Security mapping

- Integrity, complete coverage, left/right binding, depth binding, batch
  completeness, no phantom data, correct old-state passthrough,
  fresh-leaf scope: all enforced by the bus chain plus per-AIR local
  constraints.
- Cross-table soundness reduces to LogUp soundness over `α, β ∈ EF =
  BabyBear^4`, error `≤ (Σ heights) / |EF| ≈ 2^17 / 2^124 ≈ 2^{−107}` per
  bus, plus the per-AIR FRI / quotient soundness from `p3-fri` and
  `p3-uni-stark::quotient_values`.
- The batch is bound to the public root transition through the
  Bus 6 → Bus 4 → Table A → boundary chain, without being revealed to
  the verifier.

## 10. Built-in Plonky3 features used

| Feature | Crate | Use |
|---|---|---|
| `Poseidon2Air` / `VectorizedPoseidon2Air` | `p3-poseidon2-air` | Table B (`VECTOR_LEN=8` for BabyBear AVX2/NEON) |
| `LogUpGadget` (global lookups) | `p3-lookup` | Buses 1–6 |
| `LookupAir::register_lookup` | `p3-lookup` | per-AIR Send/Receive registration |
| `prove_batch` / `verify_batch` | `p3-batch-stark` | one PCS commit across all six AIRs |
| Per-instance preprocessed traces | `p3-batch-stark::common::PreprocessedInstanceMeta` | Tables A, B, C, D, E, F |
| `TwoAdicFriPcs` + `MerkleTreeMmcs<Poseidon2…>` | `p3-fri`, `p3-merkle-tree`, `p3-baby-bear` | PCS / FRI |
| `DuplexChallenger<F, Perm24, 24, 16>` | `p3-challenger` | Fiat–Shamir |
| `BinomialExtensionField<BabyBear, 4>` | `p3-baby-bear`/`p3-field` | extension for FRI / LogUp; ≈124-bit security |
| `AirBuilder::when_first_row` / `when_last_row` / `when_transition` | `p3-air` | boundary / transition gates |
| `check_constraints` | `p3-air` | per-AIR constraint debugging |

## 11. Parallelizability

Plonky3 ships ready-made rayon paths gated by the `parallel` cargo
feature on `p3-maybe-rayon`. The rsmt-air workspace enables it on
`p3-batch-stark`, `p3-uni-stark`, `p3-poseidon2-air`, `p3-dft`, and
`p3-lookup` (Cargo.toml); `p3-fri` and `p3-merkle-tree` pick it up via
feature unification. This unlocks parallel quotient evaluation,
LogUp aux trace + prefix sums, vectorized Poseidon2 trace generation,
and batch DFT.

On the rsmt side, `build_table_c` runs `par_iter` over leaves
(per-leaf sponge state never crosses the leaf boundary), and
`batch_demo` fans out the three independent witness builds
(A, F, C) and the five trace-materialization calls via nested
`rayon::join`. Tables A and F stay sequential — their
post-order, stack-based walk over the consistency-proof opcode
stream has true cross-row data dependencies.

Determinism is preserved: `prove_batch` output (`proof_KB`) is
byte-identical between serial and parallel builds with the same
challenger seed. Measured end-to-end speedup at batch=4096 is ≈4×
(see §7).

## 12. The choice of proving hash function

The proof system uses hash function internally:

- Merkle commitments for main, permutation, quotient, preprocessed, and FRI
  folded-codeword matrices.
- The FRI commit-phase MMCS through `FriParameters::mmcs`.
- The Fiat-Shamir challenger and proof-of-work grinding.

The prover exposes these as compile-time suites in
`rsmt_prover::proof_hash`:

```rust
use rsmt_prover::batch_demo::prove_and_verify_with_metrics_cfg_for;
use rsmt_prover::config::ProverConfig;
use rsmt_prover::proof_hash::{Blake3ProofHash, Poseidon2ProofHash, Sha256ProofHash};

let cfg = ProverConfig::default();
let poseidon_metrics =
    prove_and_verify_with_metrics_cfg_for::<Poseidon2ProofHash>(0, 1024, &cfg);
let sha_metrics =
    prove_and_verify_with_metrics_cfg_for::<Sha256ProofHash>(0, 1024, &cfg);
let blake3_metrics =
    prove_and_verify_with_metrics_cfg_for::<Blake3ProofHash>(0, 1024, &cfg);
```

Use `poseidon2` when this proof is intended to be recursively verified inside a
field-friendly circuit. Use `sha256` or `blake3` for a final native-CPU proof
when recursive verification is not needed.
