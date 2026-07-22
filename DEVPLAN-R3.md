# R3 development plan: security closure and proving-time optimization

Status: proposed replacement roadmap, 2026-07-18.

This is a new plan. It does not amend or continue `DEVPLAN.md`; that file is a
historical record of the rewrite that produced the current implementation. The
starting point here is the completed seven-table implementation
`A/B/C/D/R/F/P`, including end-to-end batch proving and all current LogUp
buses. The purpose of R3 is to:

1. repair the verifier/preprocessing trust boundary and the remaining
   byte-faithfulness and multiplicity defects;
2. state precisely what security the application needs, instead of demanding
   the stronger but mostly irrelevant property that every witness cell be
   uniquely constrained;
3. reduce the dominant committed and quotient-polynomial sizes without
   weakening the reference transition relation; and
4. leave a fixed, Poseidon2-based protocol suitable for a future recursive
   verifier.

The target is a clean cut-over, not wire compatibility with the current proof
format. The old prover may remain temporarily as a differential and performance
oracle, but it is not a supported protocol after the R3 verifier is released.

---

## 1. Executive decisions

The following choices are normative for R3.

| ID | Decision |
|---|---|
| R3-D1 | A key is exactly 32 bytes and a leaf value is exactly 32 bytes. At public APIs use `Key32([u8; 32])` and `Value32([u8; 32])`; field limbs are internal checked representations. Applications with variable-size payloads hash them to `Value32` outside this protocol, with application-level domain separation. |
| R3-D2 | The AIR proves computational integrity, not zero knowledge. Witnesses are not public inputs, but no confidentiality is claimed for data appearing in FRI-opened trace rows. Do not add masking columns or a hiding PCS. |
| R3-D3 | The required property is semantic soundness of the public state-transition statement. A witness cell need not be uniquely determined if changing it cannot change any public value, lookup contribution, constrained expression, hash input/output, or extracted reference execution. Dead cells should nevertheless be removed because they cost time and enlarge the audit surface. |
| R3-D4 | Keep Poseidon2 for both the in-tree hash and the default STARK commitment/transcript stack. Fix all Poseidon2 constants and FRI parameters in a versioned verifier configuration; do not accept a prover-chosen seed or proving configuration. |
| R3-D5 | Replace `A/B/C/D/R/F/P` with `A/B/L/J/O/R/P`: fuse canonical leaf input and the three-step leaf sponge into `L`; split `F` into join-only `J` and opening-only `O`; retain the fixed range table `R`, powers table `P`, opcode table `A`, and vectorized Poseidon2 table `B`. |
| R3-D6 | Put all per-proof data in main traces. Preprocessed traces must be deterministic functions only of the protocol version and a bounded public shape, or be authenticated by a verifier-owned key. In particular, neither the batch nor its digits may be supplied through `ProverData::common`. |
| R3-D7 | The correctness baseline emits one Table-B request for each logical permutation occurrence and shares only the node prefix local to one join. Global deduplication may be reintroduced only as a later measured optimization keyed by `(mode,input)`, with an explicit B sender multiplicity, exact multiplicity sums, and no-wrap checks. Never deduplicate while sending multiplicity one. |
| R3-D8 | Preserve `subtree_start`; it gives an algebraic, acyclic, contiguous post-order tree and avoids a cryptographic fixed-point assumption for trace topology. |
| R3-D9 | Canonicalize every byte-originating leaf, including `O_l`, and every opened junction region. Public digests, shapes, and proof-envelope field elements also require canonical encodings at decode time. |
| R3-D10 | Combine at most two linear lookup entries into one LogUp running-sum column where the measured total cost decreases. The resulting LogUp constraint has degree at most three. No grouping is accepted until symbolic-degree, end-to-end FRI, and adversarial balance tests pass. |
| R3-D11 | Empty-batch identity is a separate, non-STARK protocol case. It accepts only `old_root = Some(new_root)` and no opcode/batch witness. It must not create a zero-row AIR whose unconstrained boundary can certify arbitrary roots. |
| R3-D12 | Optimize for total proving wall time under the final soundness target, not main-trace width in isolation. Count main, preprocessing, extension-field LogUp columns, quotient chunks, LDE expansion, commitment construction, and padding cliffs. |
| R3-D13 | Do not reduce the documented security budget: target at least 116 bits for the standalone STARK/FRI component and at least 100 bits for the complete false-accept probability after LogUp and all union bounds. If the formal calculation cannot justify this with the chosen field/extension, increase parameters or lower the maximum shape. |

These choices deliberately relax three requirements that are not needed by the
application:

- arbitrary-length leaf values;
- zero knowledge; and
- unique determination of semantically irrelevant witness cells.

They do **not** relax canonical key placement, confinement, hash evaluation,
public-root binding, post-order topology, lookup balance, or verifier ownership
of the statement and protocol parameters.

---

## 2. Application and system model

### 2.1 Intended use

The Unicity Aggregator maintains a path-compressed sparse Merkle tree. A round
starts from an authenticated old root and adds a finite set of fresh
`(key, value)` leaves, producing a new root. A compact consistency-proof stream
opens only the preserved structure needed to justify the additions. The STARK
replaces native execution of that stream for an external verifier.

The public state for one non-empty round is:

```text
Statement = (
    protocol_id,
    old_root_is_none,
    old_root[8],
    new_root[8],
    shape
)
```

where the roots are BabyBear digests and `shape` fixes every AIR height and
every deterministic preprocessed mask. The private witness contains the opcode
stream, added leaves, opened preserved nodes and leaves, intermediate digests,
coherence decompositions, Poseidon2 evaluations, and lookup multiplicities.

“Private” in the previous paragraph means “not a public input.” R3 is not
zero-knowledge: a verifier may learn witness fragments from ordinary STARK
openings. If the deployment later requires confidentiality, that is a distinct
protocol revision with hiding commitments or trace masking and a new security
analysis.

### 2.2 What a verified round is meant to establish

Let `V_RSMT` be the abstract consistency verifier defined by the RSMT formal
model: it executes the post-order opcodes, checks coherence and confinement,
hashes opened/new objects, and ends with the claimed roots. Let `Encode32`
injectively map 32 bytes to the nine BabyBear limbs used by the hash.

The R3 relation is:

```text
R_R3(public, witness) = 1
```

iff all of the following hold:

1. `public.protocol_id` names the fixed R3 AIR, Poseidon2 constants, field,
   extension, PCS, transcript, and FRI parameters;
2. the bounded public shape is consistent with the trace domains and fixed
   preprocessing;
3. the witness decodes to a well-formed opcode execution with exact 32-byte
   keys and values and canonical opened regions;
4. that execution satisfies the RSMT digest algebra, coherence, confinement,
   and post-order rules; and
5. its final stack item is exactly the public old/new root pair, including the
   `None`/`Some([0;8])` distinction.

The batch itself is existential in the current public statement. The theorem is
therefore “there exists a set of canonical 32-byte leaves producing this
transition,” not “this externally supplied list was applied.” This matches the
current public-root-only API. If an application later needs to attest a
particular hidden batch, it must add a public batch commitment and an in-AIR
binding to it. That extension is not free and is not silently assumed here.

Eliminating the batch table requires an explicit new-leaf ordering lemma. In a
contiguous post-order tree, coherence places every advised left subtree before
every advised right subtree. Hence the `L` leaves encountered in A-row order
are in strictly increasing key order; two equal keys cannot be separated by a
valid junction. The extracted batch is precisely this ordered `L` subsequence.
R3 must prove this lemma from topology plus coherence and test it
differentially. If the lemma fails, a narrow order argument must be restored;
sorting must not be trusted merely because the honest witness builder performs
it.

### 2.3 Stateful interpretation

A proof cannot by itself establish that `old_root` is the globally accepted
state. The system theorem is inductive:

1. a genesis rule or trusted checkpoint authenticates `root_0`;
2. each accepted R3 proof establishes a valid transition from the already
   authenticated `root_i` to `root_{i+1}`; and
3. the consensus/certification layer prevents competing successors from being
   treated as the same canonical round.

If a verifier accepts an attacker-chosen old root with no chain or checkpoint,
the proof establishes only a valid transition from that attacker-chosen tree.
This is not an AIR defect and must be explicit in the integration
documentation.

### 2.4 Leaf-value semantics

`Value32` is an opaque 256-bit string. The RSMT layer does not interpret it.
Typical callers should set:

```text
Value32 = H_app(application_domain || canonical_payload)
```

The application hash and payload encoding are outside R3. The fixed-width
choice is useful:

- it makes byte-to-field encoding injective;
- it removes the present silent truncation/right-alignment ambiguity;
- it keeps every leaf at exactly three Poseidon2 permutations; and
- it avoids a length column, length-prefix rules, and a variable number of
  sponge blocks.

Arbitrary-length values therefore do not come for free. They can be introduced
only by a later versioned leaf-hash definition.

---

## 3. Security model

### 3.1 Adversary

The adversary controls the prover and all witness data. It may:

- choose malformed opcodes, leaves, openings, trace values, padding values,
  multiplicities, and permutation requests;
- choose any allowed public shape and exploit power-of-two padding cliffs;
- submit malformed or non-canonical proof bytes;
- try to mix data between rows or tables;
- repeat equal Poseidon2 inputs;
- adapt the proof to the public roots and all prior public transcripts; and
- spend bounded computation grinding commitments or Fiat–Shamir challenges.

The adversary does **not** choose:

- the verifier implementation;
- `protocol_id`, field, extension, Poseidon2 constants, transcript domain,
  FRI/PCS configuration, or lookup definitions;
- verifier-owned preprocessing commitments;
- the accepted old root in the surrounding state machine; or
- the random-oracle/cryptographic primitive internals, except through their
  specified interfaces.

### 3.2 Required security property

The primary property is computational soundness:

> For every probabilistic polynomial-time prover, the probability that the R3
> verifier accepts `(public, proof)` while no canonical witness satisfies
> `R_R3(public, witness)` is negligible in the configured security level.

At the arithmetization layer this decomposes into:

1. **AIR faithfulness:** satisfying traces extract to an accepting abstract
   RSMT execution.
2. **LogUp soundness:** a false cross-table multiset equality is accepted only
   with the bounded challenge-collision probability.
3. **STARK soundness:** the committed traces are low-degree and satisfy the
   AIR except with the configured FRI/Fiat–Shamir error.
4. **Encoding faithfulness:** extracted keys, values, regions, public fields,
   shapes, and proof elements have exactly one accepted external encoding.
5. **Hash binding:** at the tree-semantics layer, two different canonical
   objects cannot feasibly be substituted under one Poseidon2 digest.

The repository should state separately:

- an algebraic theorem, conditional on the STARK and LogUp arguments, that
  accepted traces extract to `V_RSMT`; and
- a system theorem, additionally conditional on Poseidon2 collision resistance
  and authenticated root chaining, that accepted roots have the intended tree
  meaning.

This separation avoids incorrectly claiming that collision resistance is
needed to prove an in-circuit permutation was evaluated, while still recording
where it is needed to interpret a digest as a unique tree object.

### 3.3 Completeness

For every non-empty transition accepted by the abstract verifier over
canonical `Key32`/`Value32` leaves, the witness builder must produce traces of
an allowed shape that satisfy all local constraints and global buses. Honest
transitions must not fail because of:

- duplicated Poseidon2 inputs;
- padding boundaries;
- an opening at depth `0`, `239`, `240`, or `255`;
- `None` versus a present all-zero digest;
- a one-child old-state passthrough;
- equal old/new terminal permutation inputs occurring in different logical
  places; or
- a valid distribution of `S`, `O`, `O_l`, `L`, and `N` rows.

Completeness is an explicit reason to remove the current global permutation
deduplication: two logical receives require multiplicity two even when their
tuples are equal.

### 3.4 Canonical encoding

Canonicality is required wherever an external byte object is claimed:

- key: exactly 32 bytes;
- value: exactly 32 bytes;
- opened region: exactly the `d`-bit prefix, left-aligned and zero below `d`;
- public BabyBear element: integer in `[0, p)`, encoded once;
- `old_root_is_none`: one byte or field boolean with only `0` and `1`;
- shape integer: a minimally encoded bounded unsigned integer;
- proof envelope: one protocol version and no trailing or duplicate fields.

Canonicality is not required for an internal algebraic helper that has no
external byte semantics, provided its range and relations are sufficient for
the soundness proof.

### 3.5 Semantically harmless underconstraint

“Every main cell changes a constraint when incremented” is a useful bug-finding
heuristic, not the security theorem. A locally free multiplicity in Table R,
for example, is globally fixed by LogUp balance. Conversely, a constrained
column can still be insecure if it is bound to the wrong bus tuple.

Classify every witness column into one of:

1. **statement-bearing:** reaches a public boundary;
2. **execution-bearing:** determines an extracted opcode, digest, advice, key,
   value, region, or topology edge;
3. **cryptographic:** is a Poseidon2 input/output or a continuation state;
4. **interaction-bearing:** appears in a lookup element or multiplicity;
5. **algebraic helper:** exists only to keep constraints low-degree and is
   functionally related to the above; or
6. **irrelevant:** changing it cannot affect classes 1–5 or constraint
   satisfiability.

Classes 1–5 need a documented local, boundary, or bus relation. Class 6 does
not weaken semantic soundness, but should normally be deleted. If a class-6
cell must remain for a generic upstream layout, put it on a reviewed
noninterference allowlist and prove that it never enters an expression,
lookup, public output, or extracted execution.

No R3 table should intentionally add “canonical zeroing” merely to claim total
constraint coverage if omitting the column is cheaper. Padding is different:
padding values and multiplicities must be constrained or masked wherever they
could enter an AIR or bus.

### 3.6 Assumptions and non-goals

Assumptions:

- the pinned Plonky3 batch-STARK, Poseidon2 AIR, PCS, challenger, and LogUp
  implementation behave as specified;
- the BabyBear degree and two-adicity limits are enforced;
- the extension field and number of lookup challenges meet the derived error
  bound;
- the fixed Poseidon2 instances provide the claimed collision/preimage
  resistance;
- the verifier obtains the old root from an authenticated state chain; and
- the proof decoder and resource limits run before allocation or expensive
  verification.

Non-goals:

- zero knowledge or witness indistinguishability;
- proof of transaction authorization or application payload validity;
- consensus over which valid successor root wins;
- attestation of a particular batch without a public batch commitment;
- support for variable-length values;
- post-quantum security claims beyond those justified for the chosen hashes
  and parameters; and
- backward verification of pre-R3 proof bytes.

---

## 4. Findings and required disposition

| Finding | Security effect | R3 disposition |
|---|---|---|
| Per-proof batch data is placed in Table-D preprocessing and the prover-created `ProverData::common` is passed to verification. | A real external verifier has no independent statement of what preprocessing and lookup metadata it is accepting. The current single-process demo verifies what the prover just constructed. | Eliminate D and place leaves in L main columns. Reconstruct all preprocessing from bounded public shape, or load a verifier-owned cached preprocessing key. Give proving and verification separate APIs and tests/processes. |
| Table-F opening rows do not prove full canonical regions. | The AIR relation can accept a field-level opening that is not the byte-level `O(d,p,...)` object claimed by the reference model. | Split O from J. O carries canonical radix-1024 region digits, reconstructs the nine limbs, proves the boundary and zero suffix, and hashes only those expressions. |
| Opened leaves bypass Table D and therefore bypass canonical key/value checks. | `O_l` currently proves a field-limb preimage, not necessarily an exact 32-byte leaf. | Every `L` and `O_l` is one row of the same canonical L table. |
| `pack_value_32` accepts a slice, truncates after 32 bytes, and right-aligns shorter values without a length. | Different API values can map to the same leaf hash input. | Replace it with an exact `Value32`; delete truncation and implicit padding. |
| The Poseidon2 arena globally deduplicates equal inputs while Table B sends each stored row with multiplicity one. | Two logical receives of one equal tuple can be backed by one send, breaking completeness; the present plan invariants even permit an arena smaller than the logical permutation budget. | Store one arena entry per logical evaluation occurrence. Assert exact, not upper-bounded, permutation counts. |
| A, C, and F retain witness columns that are unused for some row kinds. | Mostly audit and performance cost, not a semantic attack when the cells have no influence. | Delete obsolete link columns, fuse C/D, and split F. Replace a blanket “no underconstraint” rule with the influence classification and noninterference audit. |
| Protocol constants and FRI settings are caller-tunable; Poseidon2 proof-hash constants are derived from a caller seed. | A prover-controlled verifier configuration changes the protocol and can enable parameter downgrade or weak-instance grinding. | One fixed `ProtocolConfig`/`ProtocolId`. Fixed audited constants; no seed in `prove` or `verify`. Experimental benchmark configurations cannot produce production proof envelopes. |
| Shape fields include a per-permutation `Vec<bool>` and are accepted as ad hoc verifier inputs. | Large/non-canonical shape encodings complicate preprocessing ownership and resource limits. | Order B requests as feed-forward then terminal. Public shape carries scalar counts only and is validated before allocation. |
| Current cell metrics count only main + preprocessing and start proving after `ProverData` construction. | Optimization decisions can be wrong because extension columns, quotient work, preprocessing commitment, and setup time are omitted. | Add full polynomial/cell accounting and both cold and cached-setup wall times before accepting an optimization. |
| The empty batch is handled outside the AIR but the protocol artifact is unspecified. | Integration code may accidentally treat an empty/zero-height proof as binding arbitrary roots. | Versioned `IdentityTransition` with exact equality checks and no STARK body. |
| Proof/public serialization has no documented canonical-decoding and size policy. | Malleable encodings, ambiguous statements, or denial of service are possible even if the AIR is sound. | Add a bounded canonical envelope and negative decoding tests. |
| Dependency audit reports a current Rayon-path advisory and unmaintained/yanked transitive crates. | Supply-chain/robustness risk; not an AIR relation defect. | Upgrade or pin patched dependencies, record accepted residual advisories, and run `cargo audit` in CI. |

---

## 5. Target arithmetization

### 5.1 Tables

The target has seven AIRs:

| Table | Real rows | Purpose | Projected main width before exact indexing |
|---|---:|---|---:|
| A | one per opcode | private opcode stream, old/new digest, advice, public boundary, post-order `subtree_start` | about 33 |
| B | one vector row per `V` Poseidon2 evaluations | sole evaluator for all in-circuit Poseidon2 calls | implementation-dependent; compare 0/1 S-box registers |
| L | one per `L` or `O_l` | canonical key/value plus all three leaf-sponge requests | about 93 |
| J | one per `N` | child consumption, post-order topology, coherence, confinement, four-way old state, node hash | about 134 |
| O | one per `O` | canonical opened region and one node hash | about 88 |
| R | fixed 2048 | `R10(bits,value)` range table and multiplicities | 1 main + 2 prep |
| P | fixed 32 | `(k,2^k)` powers and multiplicities | 1 main + 2 prep |

Widths are design targets, not acceptance criteria. Exact effective cost also
includes extension and quotient columns. Layout structs remain the single
source of truth and tests must print the realized numbers.

The first-order reason for this layout is:

- A falls from 37 to about 33 main columns (about 11% before aux/quotient).
- A current new leaf occupies three C rows of width 50 plus one D row with 72
  dynamic preprocessed columns and a dummy main column: about 223 base cells
  before padding and aux. One L row is about 93 base cells. An opened leaf
  currently costs about 150 C base cells but lacks canonicality; canonical L
  is both smaller and sounder.
- If joins and openings have comparable counts `N`, the union F costs roughly
  `2N * 142 = 284N` main cells before padding details. Split J/O costs roughly
  `N * (134 + 88) = 222N`, about 22% less. The exact benefit is
  shape-dependent because each table pads separately.
- Pairing L's 52 range entries reduces 52 extension running-sum columns to 26.
  At extension degree four this saves roughly 104 base-field-equivalent cells
  per padded L row before accounting for the higher quotient degree.

The Poseidon2 evaluation count itself is already minimal for the fixed hash
definition: three calls per leaf, two per ordinary node/opening, and one extra
old-children call for `b11`, with the node prefix shared locally. R3 therefore
does not claim a sound way to remove hash calls. Its dominant-table work is to
represent and batch those unavoidable calls more cheaply.

### 5.2 Table A

Keep:

```text
selectors[5]
old[8], new[8], old_is_none
delta, rho[9]
subtree_start
```

Remove:

- `has_advice`: derive as `1 - is_s`;
- `batch_idx`: L rows bind directly by A's preprocessed `row_idx`;
- `opened_idx`: O/L helpers also bind directly by A row index; and
- `node_hash_old_needed`: J derives `b11` from child `None` flags and does not
  need to round-trip it through A.

The five selectors remain the baseline because they keep all opcode gates at
degree two. A lower-column encoded opcode may be benchmarked only if its extra
quotient cost wins end to end.

The tree bus continues to send every non-root row with its unique
preprocessed row index and `subtree_start`. The parent and leaf buses return
results keyed by the same row index. The final real row binds
`old_root`, `new_root`, and `old_root_is_none`.

### 5.3 Table L: fused canonical leaf

L replaces both C and D. One row contains:

```text
a_row_idx
key_digits[26]
value_digits[26]
mid_0[16]
mid_1[16]
digest[8]
```

The 26 radix-1024 digits encode eight 30-bit limbs and one 16-bit limb:

```text
8 * (10 + 10 + 10) + (10 + 6) = 256 bits.
```

Each digit is range-checked against R with a fixed width. The nine key and
value limbs are linear expressions, not columns. The row makes:

- one `p2ff` receive for leaf step 0, output `mid_0`;
- one `p2ff` receive for leaf step 1, output `mid_1`; and
- one `p2term` receive for step 2, output `digest[0..8]`.

It sends `(a_row_idx, digest[8], key_limbs[9])` on the leaf bus. A receives the
tuple on either `L` or `O_l` and locally imposes the different old-state rules.
The L table therefore needs no batch/opened kind bit, no leaf index, no
three-row continuity constraints, and no batch bus.

The witness builder orders L rows deterministically by `a_row_idx`. This order
is for canonical witness generation and reproducible benchmarking; LogUp
soundness relies on the row-index key, not on row order.

### 5.4 Table J: joins only

J keeps the sound R10 coherence construction and `subtree_start`, but removes
the union-layout tax and redundant scalars.

Baseline J data:

```text
parent_row_idx, left_start, right_start
depth, parent_region[9]
boundary_limb_onehot[9], r_off, pow_b
H_digits[3], u_r[3], u_k[3], width_r[3], width_k[3]
left  = (old[8], new[8], none, has, delta, rho[9], L_digits[3])
right = (old[8], new[8], none, has, delta, rho[9], L_digits[3])
parent_none, parent_old[8], parent_new[8]
prefix_mid[16]
```

Derive rather than store:

- `H` and each child tail `L` from their three digits;
- `s_r` and `s_k` from the one-hot selectors;
- `b00`, `b01`, `b10`, and `b11`, using
  `parent_none = left_none * right_none`; and
- `gap = child_delta - depth - 1`.

Retaining `width_r[3]` and `width_k[3]` is initially preferable because it
makes range lookup elements linear and permits two-entry LogUp grouping. A
candidate that derives these six columns as degree-two expressions must be
compared using total main + extension + quotient cost.

The node prefix is evaluated once and its full 16-limb output is used locally
by the new and, for `b11`, old children blocks. The new terminal digest is
always checked; the old terminal digest is checked only for `b11`. There is no
global sharing of the prefix with any other J or O row.

### 5.5 Table O: canonical opened junctions

O contains:

```text
a_row_idx
depth
region_digits[26]
boundary_limb_onehot[9], r_off, pow_b
H_digits[3], u_r[3], width_r[3]
left_digest[8], right_digest[8]
prefix_mid[16], digest[8]
```

The region limbs are linear reconstructions of fixed-width canonical digits.
The boundary constraints enforce:

```text
depth = limb_start(q) + r_off
region[j] = 0                         for j > q
region[q] = 2 * pow_b * H
H < 2^r_off
pow_b = 2^(W(q) - r_off - 1)
```

while the fixed digit ranges make every full prefix limb a canonical 30-bit
or 16-bit integer. Consequently the region is exactly a left-aligned `depth`
bit prefix and not merely a field tuple that happens to hash.

Depths `0`, `239`, `240`, and `255` receive dedicated tests. In particular,
depth zero forces the all-zero region and depth 255 forces exactly the final
low bit to zero.

O receives one full-output prefix permutation and one terminal node
permutation, then sends `(a_row_idx, digest, digest, not-none, depth, region,
subtree_start=a_row_idx)` to A over the parent bus.

### 5.6 Table B and logical permutation accounting

The exact logical permutation count is:

```text
n_perm = 3*n_leaf + 2*n_join + n_b11 + 2*n_open
```

where `n_leaf = n_L + n_Ol`. R3 requires equality with the arena length.

Store occurrences, not distinct inputs. The arena becomes:

```text
PermutationPlan {
    feed_forward: Vec<PermIo>,
    terminal: Vec<PermIo>,
}
```

This scalar segmentation makes B preprocessing a function of
`(n_ff, n_term, vector_len)` and removes `RoundShape::b_modes: Vec<bool>`.
Table B sends the first segment on `p2ff` and the second on `p2term`; padding
lanes have zero multiplicity.

The initial implementation keeps the current Poseidon2 AIR parameters. A later
measured milestone compares:

- `P2_SBOX_REGISTERS = 1` versus `0`;
- vector lengths `4`, `8`, and `16`;
- grouping adjacent B sends two per LogUp context; and
- the quotient/FRI configurations required by each maximum degree.

`SBOX_REGISTERS=0` approximately halves the per-permutation main width but
raises the Poseidon2 constraint degree. It is not considered an optimization
until quotient generation, LDE, proof size, and wall time all have been
measured.

A multiplicity-aware arena is a legitimate later candidate: one B evaluation
can back `m` identical logical calls if it sends the tuple with multiplicity
`m` on the correct mode bus. This requires a main multiplicity per B lane,
checked total counts, and deduplication keyed by `(feed-forward/terminal,
input)`. The occurrence-per-row design lands first because it is the simplest
completeness oracle. Keep the deduplicated variant only if repeated inputs save
enough padded B rows to beat the extra columns and planning work on the agreed
corpus.

### 5.7 Tables R and P

Retain:

```text
R = {(bits, value) | 0 <= bits <= 10, 0 <= value < 2^bits}
P = {(k, 2^k) | 0 <= k <= 30}
```

Their multiplicity columns are intentionally not locally determined. They are
interaction-bearing cells fixed by global lookup balance. Padding rows must
have fixed tuple values and zero effective multiplicity.

A possible 256-row combined depth/boundary table is not the baseline. It saves
some J/O helper constraints but adds wider tuples, more fixed preprocessing,
and another multiplicity family. Benchmark it only after the simpler R/P
design is correct and fully costed.

### 5.8 Physical buses

| Bus | Tuple | Direction |
|---|---|---|
| `tree` | `(row_idx, subtree_start, old[8], new[8], old_none, has_advice, delta, rho[9])` | A non-root rows → J left/right |
| `parent` | `(row_idx, old[8], new[8], old_none, delta, rho[9], subtree_start)` | J/O → A `N`/`O` |
| `leaf` | `(row_idx, digest[8], key[9])` | L → A `L`/`O_l` |
| `p2ff` | `(input[16], output[16])` | B → L/J/O feed-forward calls |
| `p2term` | `(input[16], digest[8])` | B → L/J/O terminal calls |
| `range` | `(bits, value)` | R → J/O/L |
| `pow2` | `(k, 2^k)` | P → J/O |

There is no batch bus. Advice and digest remain in the same tree/parent tuple,
so a prover cannot combine one subtree's hash with another subtree's
placement. Row indices are verifier-fixed in A preprocessing and unique on
real rows. A needs no independent depth lookup: `S` fixes depth to zero,
`L/O_l` fix it to 256, and `N/O` receive a depth already range-checked by J/O.

### 5.9 Two-entry LogUp grouping

The pinned Plonky3 LogUp implementation supports several lookup inputs in one
context. For two entries with linear compressed elements `a,b` and linear
multiplicities `m_a,m_b`, it enforces a common denominator:

```text
(alpha-a)(alpha-b)
```

and a numerator:

```text
m_a(alpha-b) + m_b(alpha-a).
```

The transition constraint has degree at most three because the running-sum
difference is degree one. This trades one extension-field running-sum column
for a higher, but still allowed, degree.

Apply pairing only within the same physical bus and AIR, never across bus
names. Expected candidates include:

- L's 52 fixed digit checks: 52 → 26 contexts;
- L's two `p2ff` calls: 2 → 1;
- O's fixed region digit checks: up to 26 → 13;
- J's H/tail/gap checks in compatible linear pairs; and
- adjacent B lanes with the same feed-forward/terminal mode.

Do not group three entries: its denominator is cubic and the transition
constraint is generally degree four. Do not pair degree-two tuple elements
without re-deriving the degree. The old `OodEvaluationMismatch` experience is
treated as a regression target: every paired candidate must have a minimal
full-FRI test before it is used in the round AIR.

---

## 6. Verifier-owned protocol and preprocessing

### 6.1 Protocol identifier

Define a stable identifier covering at least:

```text
field and extension polynomial
RSMT opcode semantics
key/value and region encodings
leaf/node hash domains and Poseidon2 constants
AIR table set and column layouts
bus names and tuple order
PCS/MMCS/challenger constructions and constants
FRI parameters and security target
proof-envelope version
```

Changing any item creates a new protocol ID. The ID is absorbed into the
Fiat–Shamir transcript or otherwise cryptographically bound before challenges.
It is not merely an informational string in the serialized envelope.

### 6.2 Public shape

Use scalar counts only, for example:

```text
RoundShape {
    n_ops,
    n_leaf,
    n_join,
    n_open,
    n_b11,
    n_p2ff,
    n_p2term
}
```

The verifier recomputes all padded heights and checks algebraic count
identities, including the exact permutation formula. Redundant fields may be
removed after implementation; if retained, disagreement is a decode error.

Before allocating, reject shapes that violate:

- protocol maximum real/padded height;
- BabyBear's two-adic domain limit;
- row-index injectivity in BabyBear;
- serialized proof-size limits;
- exact opcode/helper count relations;
- `n_b11 <= n_join`;
- exact Poseidon2 request counts; or
- any per-bus total multiplicity greater than or equal to the BabyBear order.

The last check prevents multiplicities from wrapping modulo the base field.
Compute the exact maximum contribution of each bus from the shape; do not use a
single informal “reasonable batch size” assumption.

### 6.3 Setup and cache

Preprocessed columns for A/B/L/J/O are functions of shape: row index, realness,
last-row markers, and B mode masks. R/P preprocessing is protocol-fixed.

Provide:

```text
prepare_verifier(shape, protocol) -> VerifierData
prepare_prover(shape, protocol)   -> ProverData
prove_round(prover_data, publics, witness) -> ProofEnvelope
verify_round(verifier_data, publics, envelope) -> Result
```

`VerifierData` is created without witness access. It may be:

- deterministically recomputed and committed by the verifier; or
- loaded from a trusted cache keyed by `(protocol_id, canonical_shape)`.

Tests must serialize a proof in one process and verify it in another process
that receives only protocol constants, public roots, shape, and proof bytes.
No object returned by the prover setup path may be passed directly into this
verification test.

Measure both:

- **cold proof:** includes preprocessing generation and commitments; and
- **cached-shape proof:** amortizes verifier/prover setup for a repeated shape.

Both remain sound because the cache key is verifier-derived.

### 6.4 Fixed Poseidon2 proving configuration

Delete the production `seed` parameter and caller-selected `ProverConfig`.
Generate and check in the audited constants used by the width-16/24
permutations. Experimental binaries may instantiate alternative constants or
FRI parameters, but their output type cannot be decoded as a production R3
proof.

Poseidon2 remains the production commitment/transcript choice to preserve a
field-friendly recursive-verification path. Native SHA-256/Blake3 results may
remain as benchmark comparisons, not accepted R3 protocol variants.

Prefer a no-grinding candidate with enough FRI queries over
`100 queries + 16 query-PoW bits`, because grinding is expensive and awkward
inside a recursive verifier. The final choice must come from the formal
soundness calculation and benchmark grid; `116 queries, 0 PoW bits` is a
candidate, not a theorem.

### 6.5 Canonical proof envelope

Define a bounded decoder for:

```text
ProofEnvelope {
    protocol_id,
    statement,   // old-none flag, roots, and shape
    stark_proof
}
```

Requirements:

- exact protocol version;
- canonical little- or big-endian integer encoding, specified once;
- every BabyBear element decoded from an integer `< p`;
- every extension element decoded from canonical base coefficients;
- no duplicate fields, ignored trailing bytes, or alternate boolean forms;
- lengths checked before allocation and multiplication;
- exact correspondence between declared shape and proof openings; and
- transcript binding of protocol ID, shape, and public roots.

There is one authoritative canonical statement encoding. If
`verify_round` also receives an expected statement from the state-chain
caller, it first requires byte-for-byte/canonical-value equality with the
envelope statement; it does not maintain two independently interpreted public
input formats.

If upstream `serde`/`bincode` does not guarantee these properties, wrap or
replace it at the protocol boundary. Internal benchmark serialization is not a
production decoder.

---

## 7. Soundness proof obligations

The implementation is not complete until each lemma below has a code-level
mechanism and a negative test.

### S1. Opcode partition

Every real A row has exactly one opcode; no padding row has one. Opcode-specific
old/none/advice rules follow. The last real row exists for a non-empty proof and
is the unique public boundary.

### S2. Contiguous post-order topology

For every J row at parent A index `i`, the right child is `i-1`, the left child
is `right.subtree_start-1`, and the parent inherits the left start. Every
non-root A row is consumed exactly once on the tree bus and the root start is
zero. Therefore indices strictly decrease along child edges and all real rows
form one spanning post-order tree. Together with S6, the in-order/post-order
placement of advised subtrees makes the A-order subsequence of `L` keys
strictly increasing. This supplies the canonical extracted batch without a
separate D table.

### S3. Advice/digest co-binding

Each child tuple contains digest, `None`, depth, region, and `subtree_start`
together. Parent and leaf helper returns are keyed by the unique A row index.
No satisfying assignment can re-pair placement advice from one object with a
digest from another.

### S4. Leaf byte faithfulness

Every L digit is in its fixed radix range. Linear reconstruction is injective
to exactly 32 key bytes and exactly 32 value bytes. All three Poseidon2 requests
use those expressions, and the terminal digest returned to A is the checked
output.

### S5. Opened-region faithfulness

O's digits are canonical, the depth is in `[0,255]`, all limbs below the
boundary are zero, and the boundary has exactly `r` possible prefix bits
followed by zeros. The node prefix permutation and parent tuple use the same
region expressions.

### S6. Join coherence

For each advised child:

```text
child_delta > parent_depth
child_region[0..d) = parent_region
child_region[d] = side
```

The R10 bounds make the boundary equations integer equations rather than
ambiguous field equalities. At least one child is advised; both are advised for
a new junction.

### S7. Four-way old state

Child `None` bits select exactly:

```text
00 -> parent old None
01 -> right old passthrough
10 -> left old passthrough
11 -> Poseidon2(old left, old right)
```

The new parent always uses Poseidon2(new left, new right). The same checked
prefix state is used for old and new at that junction.

### S8. Permutation occurrence balance

Every logical leaf/join/opening permutation creates exactly one B send and
exactly one consumer receive, except the intentionally single join prefix used
locally by both children blocks. Equal inputs in distinct logical positions
remain distinct multiset occurrences.

### S9. Range and power integrity

Every range/power receive balances the corresponding fixed table entry, table
multiplicities are zero on padding, and total multiplicities cannot wrap in
BabyBear. Variable-width decompositions have range constraints on all digits
needed for uniqueness.

### S10. Verifier independence

The verifier's AIRs, lookups, preprocessing commitment, protocol constants, and
public inputs are derivable without witness/prover objects. Replacing any
prover preprocessing with a different commitment or lookup definition is
rejected.

### S11. STARK/transcript binding

Protocol ID, canonical shape, public roots, preprocessing commitment, main
commitment, lookup challenges, quotient commitment, and FRI transcript appear
in the intended order with no prover-controlled parameter downgrade.

### S12. Extraction theorem

From S1–S11, define a deterministic extraction from real A/L/J/O rows to a
canonical abstract execution. Prove on paper that the extracted execution
satisfies `R_R3`. The proof may quotient away class-6 irrelevant cells; it must
not assume they are uniquely constrained.

---

## 8. Performance model and optimization policy

### 8.1 What to count

For each table report:

```text
real rows
padded rows
main base-field columns
preprocessed base-field columns
LogUp extension columns, weighted by extension degree 4
constraint degree
quotient chunks / quotient committed columns
LDE domain size
commitment leaves and Merkle hash count
trace-fill bytes and peak resident memory
```

Round timings:

```text
reference execution
witness planning
main trace fill
preprocessing generation
preprocessing commitment
main commitment
LogUp auxiliary generation
quotient generation/commitment
FRI folding/opening
proof serialization
verification
total cold prove
total cached-shape prove
```

The current `cells = padded_height * (main + prep)` metric remains a useful
line item but is not “total cells.”

### 8.2 Benchmark corpus

Use deterministic scenarios that expose different ratios:

- genesis inserts;
- prefilled sizes `2^10`, `2^16`, and the largest practical reference size;
- batches `1, 2, 16, 64, 256, 1024` and a throughput-scale batch;
- random keys;
- deep common-prefix keys;
- rounds rich in `O`, rich in `O_l`, and rich in `b11`;
- power-of-two boundary cases where `n_join+n_open` just crosses a padding
  cliff; and
- deliberately repeated logical Poseidon2 inputs for completeness testing.

Report medians and dispersion over warmed repetitions on a pinned machine with
CPU model, thread count, compiler, profile, and commit hash recorded.

### 8.3 Optimization acceptance rule

An optimization is merged only when:

1. all soundness/completeness tests remain green;
2. symbolic maximum degree and quotient chunks are recorded;
3. it improves total prove time or the explicitly chosen secondary metric on
   the representative corpus;
4. it does not introduce a new verifier-controlled-data violation;
5. peak memory does not regress beyond an agreed bound; and
6. the result is stable, not a single noisy measurement.

Column reduction alone is insufficient. For example, deriving six J width
columns may save base cells but prevent two-entry LogUp grouping and add more
extension cells.

### 8.4 Optimization order

Apply changes in this order so effects remain attributable:

1. D+C fusion and F split;
2. removal of dead/redundant columns;
3. occurrence-correct B arena segmentation;
4. two-entry LogUp grouping;
5. B vector length;
6. Poseidon2 S-box register count;
7. FRI blowup/query/arity/final-poly parameters at the fixed security target;
8. parallel trace fill and allocation reuse; and
9. setup/preprocessing caching.

Do not mix semantic rewrites and low-level tuning in one benchmark commit.

---

## 9. Iterative implementation roadmap

Every milestone ends in a green workspace. Build R3 modules alongside the old
pipeline until the R3 end-to-end proof works; then remove the old path in one
reviewable cut-over. Old proof bytes are never accepted by the new verifier.

### M0 — freeze the theorem, protocol scope, and baseline

Deliverables:

- [ ] Add a security-model document derived from Sections 2–3 of this plan.
- [ ] Write the exact abstract R3 relation and extraction vocabulary
      independently of table names.
- [ ] Record the stateful old-root assumption and public-batch-commitment
      non-goal.
- [ ] Prove or cite the RSMT-level theorem connecting coherent additions to
      append-only tree semantics.
- [ ] Validate R3-D13 with a calculation that combines STARK/FRI, LogUp, and
      Fiat–Shamir errors. Do not rely only on
      `log_blowup * queries + PoW`.
- [ ] Define maximum shapes and per-bus no-wrap formulas.
- [ ] Capture current release benchmarks with full phase timings where
      possible, plus existing main/prep metrics.
- [ ] Preserve golden roots/opcode streams for representative rounds so the
      R3 core can be compared against the current implementation.
- [ ] Mark the existing combined `prove_and_verify_round` API experimental and
      unsuitable as an external-verifier security boundary.

Exit criteria:

- reviewers can state exactly what an accepted proof means and does not mean;
- every assumption has an owner outside or inside this repository;
- baseline artifacts and commands are reproducible; and
- no R3 code has yet changed the reference semantics.

### M1 — canonical domain types and reference semantics

Deliverables:

- [ ] Introduce `Key32`, `Value32`, checked `Digest`, and checked `Depth`.
- [ ] Change `KeyValue` and `Op::OL` to exact `Value32`; delete every
      `Vec<u8>` leaf value from protocol APIs.
- [ ] Replace `pack_value_32(&[u8])` with an injective exact-width conversion.
- [ ] Keep limb conversion private or expose only a checked constructor;
      reject limbs wider than `30,...,30,16` bits.
- [ ] Specify the canonical external byte order and add round-trip tests.
- [ ] Clarify the existential-batch semantics in the CPU verifier. Remove
      operational sorting requirements only after proving the topology +
      coherence new-leaf ordering lemma; otherwise add a narrow algebraic order
      argument without making sorting trusted verifier preprocessing.
- [ ] Add golden tests distinguishing:
      short/long values rejected, leading zero bytes retained, all-zero value,
      `None` old root, and `Some([0;8])`.
- [ ] Add differential property tests between byte operations, limb
      operations, and Poseidon2 leaf hashes.

Exit criteria:

- no accepted leaf value can truncate, pad implicitly, or alias another byte
  value;
- all reference tests use fixed 32-byte values; and
- the current and R3 reference executions agree on the retained semantics.

### M2 — production protocol/configuration and decoder skeleton

Deliverables:

- [ ] Define `ProtocolId::R3Poseidon2` and fixed checked-in Poseidon2
      commitment/challenger constants.
- [ ] Remove production seed/config parameters from the new API.
- [ ] Define canonical `RoundPublicInputs`, `RoundShape`, and
      `ProofEnvelope` encodings with explicit size limits.
- [ ] Implement shape validation and exact padded-height/count derivation
      before allocation.
- [ ] Implement canonical base/extension field decoding and reject trailing
      bytes.
- [ ] Add transcript domain-separation tests: changing protocol ID, shape,
      old-none flag, or either root changes the transcript and invalidates the
      proof.
- [ ] Add malformed-envelope fuzzing and allocation-limit tests.

Exit criteria:

- production verification cannot select a hash suite, seed, FRI parameters, or
  lookup definition from proof bytes;
- every malformed/cross-version envelope is rejected before expensive work;
- benchmark-only protocols have distinct Rust types or IDs.

### M3 — R3 witness plan and occurrence-correct permutation arena

Create new R3 row-plan structs without reusing legacy `ARow/FJoin/FOpen/CLeaf/
DRow` fields by position.

Deliverables:

- [ ] New A plan with no `batch_idx`, `opened_idx`, `has_advice`, or
      `node_hash_old_needed`.
- [ ] New one-row leaf plan with canonical digits, two mids, digest, and A row
      index.
- [ ] New separate J and O plans with the derived-column policy in Section 5.
- [ ] Replace `Arena::intern`/`HashMap` with append-only logical occurrence
      recording and separate feed-forward/terminal vectors.
- [ ] Intentionally compute a J prefix once and reference its mid locally for
      both children requests.
- [ ] Assert exact permutation counts and exact feed-forward/terminal counts.
- [ ] Build exact R/P multiplicities from planned receives using checked
      integer addition.
- [ ] Validate no per-bus count reaches the BabyBear order.
- [ ] Self-check each plan by extracting an abstract execution and running the
      reference verifier.
- [ ] Add a regression with two identical logical permutation inputs whose
      required multiplicity is two.

Exit criteria:

- every accepted reference round builds an R3 plan;
- exact permutation and lookup occurrence accounting holds;
- serial and parallel plan generation are deterministic;
- no global dedup remains.

### M4 — fused L AIR

Deliverables:

- [ ] Implement the `#[repr(C)]` L layout with widths generated from the
      struct.
- [ ] Reconstruct key/value limbs as expressions from 52 digits.
- [ ] Register all fixed-width R receives.
- [ ] Register two full-state and one terminal Poseidon2 receives.
- [ ] Send the row-indexed leaf tuple to A.
- [ ] Constrain padding or mask every padding interaction.
- [ ] Symbolically assert the documented maximum degree.
- [ ] Positive local/bus tests for both `L` and `O_l` consumers.
- [ ] Negative tests: every digit above range, wrong top-six-bit digit, wrong
      mid, wrong terminal digest, key/value digit swap, wrong A row index,
      and nonzero padding multiplicity.

Exit criteria:

- all leaf objects accepted by the AIR extract to exact `Key32/Value32`;
- no C/D/batch-bus dependency exists in the R3 path;
- leaf permutation count is exactly three per real L row.

### M5 — split J AIR

Deliverables:

- [ ] Port `subtree_start`, child tree-bus receives, coherence, confinement,
      and four-way old-state rules into a join-only layout.
- [ ] Derive H/tails, case bits, gaps, and offset remainders rather than
      storing them.
- [ ] Keep only helper widths justified by degree/LogUp cost.
- [ ] Bind prefix mid on `p2ff`, new digest on `p2term`, and old digest on
      `p2term` iff `b11`.
- [ ] Send the parent tuple to A without `node_hash_old_needed`.
- [ ] Prove all field equalities used as integer equalities are range-bounded
      below the BabyBear modulus.
- [ ] Test every boundary limb and both advised/unadvised child patterns.
- [ ] Port the shadow-insertion and re-recording attacks as full J negatives.
- [ ] Add targeted mutations for all case bits, passthrough paths, prefix
      agreement, side bit, depth gap, power, child advice/digest coupling, and
      subtree starts.

Exit criteria:

- the J soundness lemmas S2, S3, S6, and S7 have explicit tests and written
  proof notes;
- projected width and actual aux contexts are reported;
- current F remains only in the old path.

### M6 — canonical O AIR

Deliverables:

- [ ] Implement region digits and fixed digit ranges.
- [ ] Reconstruct all nine limbs as expressions.
- [ ] Enforce the selected boundary limb, zero suffix, boundary power, and
      `H < 2^r`.
- [ ] Use the reconstructed region in both Poseidon2 input and parent bus.
- [ ] Add exhaustive depth tests for all 256 depths over random prefixes.
- [ ] Add negatives for nonzero lower limb, nonzero boundary suffix bit,
      oversized prefix limb/digit, wrong q/r/power, and hash/parent mismatch.
- [ ] Compare the AIR's accepted region set against
      `is_canonical_region` by property testing.

Exit criteria:

- O accepts exactly canonical byte regions, not merely honest builder output;
- depth/canonicality equivalence passes exhaustive depth coverage;
- J and O no longer share a union layout.

### M7 — A/B integration, verifier-owned preprocessing, end-to-end R3

Deliverables:

- [ ] Implement reduced A and the seven physical bus definitions.
- [ ] Modify B to consume segmented occurrence lists and derive masks from
      scalar shape counts.
- [ ] Reuse R/P with verifier-fixed preprocessing and checked multiplicities.
- [ ] Build every AIR and preprocessing trace from `ProtocolId + RoundShape`
      without witness access.
- [ ] Implement separate `prepare_*`, `prove_round`, and `verify_round` APIs.
- [ ] Add the cross-process verification test with no shared `ProverData`.
- [ ] Ensure proof/public/shape transcript absorption is canonical and ordered.
- [ ] Implement `IdentityTransition` and reject empty STARK witnesses.
- [ ] End-to-end positive corpus: genesis, one leaf, mixed rounds, deep
      prefixes, openings, opened leaves, every old-state case, and padding
      cliffs.
- [ ] End-to-end negatives: wrong roots/none flag/shape/protocol, truncated
      proof, altered preprocessing commitment, reordered lookup metadata, and
      malformed envelope.

Exit criteria:

- an independently constructed verifier accepts honest R3 proofs;
- no prover-owned preprocessing or lookup object crosses the API;
- all current reference scenarios prove and verify under R3;
- old proof bytes fail R3 decoding.

### M8 — semantic influence audit and adversarial closure

Replace the old blanket column sweep with two complementary tools.

Deliverables:

- [ ] Generate a column-influence manifest from layout and lookup definitions:
      public boundary, local constraints, bus elements/multiplicity, hash
      requests, and extraction use.
- [ ] Fail CI if a new main column has no influence classification.
- [ ] Maintain a minimal reviewed noninterference allowlist only for unavoidable
      generic upstream cells.
- [ ] Run perturbation sweeps for classes 1–5, but allow a mutation to be
      harmless only when the extractor output and every interaction are
      unchanged.
- [ ] Bus sweep: remove/duplicate each send or receive, swap tuple fields,
      reuse one sender for two occurrence rows, and alter R/P multiplicities.
- [ ] Differential fuzzing:
      honest reference transitions must prove; mutated rejected transitions
      must fail plan construction or proof verification.
- [ ] Constraint mutation testing: temporarily delete/gate each named
      constraint family and require at least one negative test to become
      accepting.
- [ ] Fuzz canonical proof decoding separately from algebraic witnesses.
- [ ] Run a sampled subset through full FRI; run the full matrix through fast
      local constraints plus exact LogUp balance.

Exit criteria:

- every soundness lemma S1–S12 maps to code, tests, and a proof-note section;
- the influence allowlist contains no repository-defined dead columns;
- no mutated reference-rejected execution verifies.

### M9 — LogUp pairing and algebraic column optimization

Deliverables:

- [ ] Add a minimal pinned-Plonky3 test proving/verifying two linear lookup
      inputs in one global LogUp context.
- [ ] Assert the resulting symbolic degree and quotient chunk count.
- [ ] Pair L fixed digit checks and the two L `p2ff` receives.
- [ ] Pair compatible O/J range receives and adjacent B sends.
- [ ] Recompute lookup challenge union bounds for the new context count.
- [ ] Benchmark paired versus unpaired on the full corpus.
- [ ] Benchmark J/O materialized-width columns versus degree-two derived
      widths, including extension/quotient cost.
- [ ] Benchmark a mode-keyed, multiplicity-aware B arena against the
      occurrence baseline. Assert that sender multiplicity sums equal the exact
      logical permutation formula and test equal inputs across both modes.
- [ ] Keep the faster sound variant and delete the loser, rather than retaining
      runtime modes in the production protocol.

Exit criteria:

- every retained context has at most two entries and documented degree;
- the historical OOD mismatch is covered by regression tests;
- measured total prove time improves or the pairing is not merged.

### M10 — Poseidon2 and FRI parameter search

Run a controlled compile-time grid:

```text
S-box registers: 0, 1
vector length:   4, 8, 16
log blowup:      values permitted by the resulting degree
max log arity:   2, 3, 4 where supported
queries/PoW:     configurations meeting the fixed soundness target
```

Deliverables:

- [ ] Record B main width, constraint degree, quotient chunks, padding waste,
      peak memory, proof size, and each proving phase for every candidate.
- [ ] Include Poseidon2 preprocessing/MMCS work and recursive-friendliness in
      the decision.
- [ ] Prefer zero query PoW if it is faster and meets the same soundness target.
- [ ] Fix one winning configuration and check its constants/config into the
      protocol ID.
- [ ] Remove production runtime switches for vector length, S-box registers,
      FRI parameters, and proof hash.
- [ ] Keep a benchmark-only matrix for future Plonky3 upgrades.

Exit criteria:

- the production configuration is the fastest measured sound Poseidon2
  candidate on the agreed corpus, subject to memory limits;
- a written calculation supports the final security estimate;
- recursive verification remains feasible without committing to implementing
  recursion in R3.

### M11 — cut-over, documentation, dependencies, and release audit

Deliverables:

- [ ] Replace README architecture/security claims with the R3 implementation.
- [ ] Write an exact AIR specification: columns, constraints, degrees,
      preprocessing ownership, buses, and extraction proof.
- [ ] Document non-ZK behavior prominently.
- [ ] Document the 32-byte value contract and application hashing guidance.
- [ ] Document identity transitions, root chaining, shape/resource limits, and
      public-batch-commitment non-goal.
- [ ] Remove C, D, F, the unsound multiplicity-one arena dedup, old round
      demos, seed-based production config, and stale comments/tests. If M9
      selects multiplicity-aware dedup, keep only that audited implementation.
- [ ] Keep the old implementation only in a tagged git revision, not dormant
      production modules.
- [ ] Run `cargo fmt`, workspace tests, release end-to-end tests, clippy, audit,
      decoder fuzzing, and the benchmark corpus.
- [ ] Upgrade or patch the Rayon/crossbeam advisory path and review
      unmaintained/yanked dependencies; document any temporary exception with
      exploitability and expiry.
- [ ] Perform an independent review using only the final spec and code, not
      this plan.

Exit criteria:

- no stale document describes D as verifier preprocessing or F as canonical;
- production exposes only independent prove/verify APIs;
- all security, completeness, performance, and dependency gates are green;
- final benchmark and proof-size results are committed with environment
  metadata.

---

## 10. Test and review matrix

| Area | Positive tests | Negative/adversarial tests |
|---|---|---|
| Values | all-zero, leading-zero, random 32-byte values | 0–31 bytes, 33+ bytes, truncation attempts, alternate length encodings |
| Keys | byte/limb round trips, boundary bits | oversized limbs/digits, endian reversal |
| Regions | all 256 depths, random canonical prefixes | nonzero suffix, wrong boundary bit/power, out-of-range limb |
| Topology | every opcode mix, deep trees, padding cliffs | duplicate child use, forward edge, cycle attempt, bad `subtree_start`, orphan row |
| Coherence | left/right sides, one/both advice, every old-state case | `delta<=d`, side flip, region disagreement, no advice, confinement escape |
| Hashing | exact logical permutation formula | forged mid/digest, wrong mode, one send backing two equal receives |
| LogUp | honest exact multiplicities, paired contexts | missing/extra/swapped entries, field-wrap boundary, padding multiplicity |
| Public boundary | genesis/non-genesis, present zero digest | wrong root, wrong none flag, last-row/root substitution |
| Preprocessing | verifier rebuild/cache hit | prover-supplied batch/mask/common data, cache-key collision, altered lookup order |
| Protocol | fixed Poseidon2 R3 envelope | seed/config downgrade, cross-protocol replay, transcript omission |
| Decoder | canonical round trip at maximum allowed shape | noncanonical fields/booleans/lengths, trailing bytes, oversized allocation |
| Completeness | repeated equal P2 inputs in different logical locations | global dedup regression |
| Noninterference | extractor-equivalent permitted generic cells, if any | any unclassified repository column |

At least one full proof/verification test must represent each row above; fast
tests may cover the exhaustive variants.

---

## 11. Risk register

| Risk | Detection | Response |
|---|---|---|
| Split J/O loses on tiny rounds because each table pads separately. | Cost model and batch-1/2 benchmarks. | Keep the fixed split for auditability unless the agreed workload makes it materially worse. If a second layout is ever justified, give it a distinct protocol ID; do not let the prover choose an unbound layout. |
| Fused L raises row width enough to lose despite fewer rows. | Compare full C+D versus L polynomial and wall-time cost, including aux/quotient. | Retain one-row L unless a measured alternative is faster; any alternative must canonicalize opened and new leaves identically and keep witness data out of preprocessing. |
| Two-entry LogUp causes degree/OOD failures. | Minimal full-FRI regression and symbolic-degree assertion. | Keep one entry per context for that family. Correctness precedes aux savings. |
| `SBOX_REGISTERS=0` saves main cells but increases quotient cost. | M10 full-phase benchmark. | Select the measured winner; no prior commitment to register count. |
| Shape permits multiplicity wrap or row-index collision. | Exact checked formulas before setup/allocation; boundary tests at max-1/max. | Lower protocol maxima and reject the shape. |
| Removing explicit batch ordering changes the abstract relation. | Formal equivalence review and differential property tests. | State the existential-set relation explicitly. If an application needs a committed ordered batch, add a versioned public batch commitment rather than smuggling order through preprocessing. |
| Canonical decoder assumptions are false for upstream serde. | Byte-level malleability tests and source audit. | Add a custom bounded codec/wrapper. |
| Verifier cache accidentally keys only by height. | Cross-protocol/shape collision tests. | Key by protocol ID plus complete canonical shape and verify stored commitment metadata. |
| Poseidon2 constants remain seed-derived. | Production API/type audit and known-constant tests. | Check constants into source/artifacts and remove the seed path. |
| “No ZK” is misunderstood as “inputs remain confidential.” | API/docs review. | Use explicit non-confidential wording and avoid `zk` names. |
| Security estimate relies on an informal ethSTARK heuristic. | M0/M10 written soundness calculation review. | Increase parameters conservatively or obtain specialist review before release. |
| Plonky3 pin contains a security or correctness defect. | Dependency audit, upstream changelog review, reproducible vectors. | Upgrade in an isolated branch; rerun degree, adversarial, and benchmark suites before changing protocol ID. |

---

## 12. Definition of done

R3 is complete only when all of the following are true:

1. The production verifier independently reconstructs or loads authenticated
   preprocessing and never consumes prover-created `common` data.
2. Accepted leaf keys and values correspond injectively to exact 32-byte
   strings; accepted opened regions are canonical for their depths.
3. Equal logical Poseidon2 inputs have correct multiset multiplicity.
4. The extraction argument establishes the intended public-root transition
   without relying on every witness cell being uniquely determined.
5. The proof envelope, public inputs, shape, constants, and FRI configuration
   are versioned, canonical, bounded, and transcript-bound.
6. Empty identity transitions cannot bind unequal or absent old roots.
7. The complete adversarial matrix and differential fuzzing pass.
8. The selected `A/B/L/J/O/R/P` implementation is the fastest measured sound
   Poseidon2 configuration on the agreed workload, with full polynomial and
   wall-time accounting.
9. Documentation states the system assumptions, non-ZK status, fixed-value
   contract, existential-batch scope, and recursive-proof option accurately.
10. The legacy C/D/F protocol and mutable production configuration are gone,
    and dependency/security audits have no unexplained high-severity findings.

The central review question is then not “is every cell constrained?” but:

> Can any efficiently constructed accepted proof denote something other than a
> canonical, coherent RSMT transition from the authenticated old root to the
> public new root under the fixed R3 protocol?

R3 is ready only when the answer is supported by the extraction argument,
the independent-verifier boundary, adversarial tests, and measured
implementation—not by witness-generator honesty.
