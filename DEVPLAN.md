# Development plan: rsmt-air rewrite to the rsmt6a design

Target: rewrite this workspace so that the tree structure, data encodings,
algorithms, and the arithmetized statement match `ndsmt-experiments/rsmt6a.py`
and the design in `README.md`. Greenfield: **no backward compatibility** with
the current (structural, depth-only) implementation; legacy code is deleted,
not deprecated. Performance numbers will be re-measured from scratch on a new
platform.

Guiding priorities, in order:

1. **Soundness of the arithmetization** — no underconstrained columns, no
   unbalanced bus corner, every reference-verifier rule covered by a
   constraint or a bus. Every phase below ends with negative tests.
2. **Performance** — Table B (Poseidon2) dominates; everything data-dependent
   is precomputed outside the circuit so trace generation is a straight fill,
   and the permutation count is minimized (shared prefix blocks).
3. **Clarity** — column layouts as typed structs, one source of truth for
   every constant, spec (`rsmt-air.md`) regenerated from the implementation
   at the end.

Reference documents: `README.md` (table design), `rsmt-air.md` (to be
rewritten in M7), `p3-docs.md` (Plonky3 API: AIR authoring, LogUp buses,
batch-stark, degree budget), `ndsmt-experiments/rsmt6a.py` (reference
semantics), aggregation-layer paper (what the statement means — out of scope
here, but the CPU verifier must match it).

---

## 0. Global decisions (fix these first, everything depends on them)

| # | Decision | Choice |
|---|---|---|
| D1 | Bit order | Plain **MSB-first**, as in rsmt6a.py. Delete `sort_key.rs` bit-reversal; the traversal sort key is the big-endian key bytes themselves. |
| D2 | Key type in hot paths | `[u8; 32]` at API edges, `[u32; 9]` limbs internally (limbs 0..7 = 30 bits, limb 8 = 16 bits, **limb 0 = most significant**). `BigUint` only in tests/CLI parsing. |
| D3 | Region representation | Same 9-limb packing as keys, of the value `region << (256 − d)` — left-aligned, zero-filled below bit `d`. A leaf's region is its key limbs verbatim. One canonical encoding per region. |
| D4 | Node hash | Two-permutation sponge: prefix block `P2([DOMAIN_NODE, d, p[0..9], 0×5])`, then children block `P2(mid + left‖right)`; digest = first 8 limbs. Prefix block shared between old/new digests of one junction. |
| D5 | Leaf hash | Unchanged 3-step sponge (`DOMAIN_LEAF`, key, value; rate 8 / capacity 8). |
| D6 | Empty digest | `None` ↔ canonical all-zero 8 limbs at the public boundary; `Op::S` never carries it (builder + AIR reject). Empty-batch identity transition handled by the caller, not the AIR. |
| D7 | Opcode set | `S(digest)`, `O{d, region, c_l, c_r}`, `OL{key, value}`, `L`, `N{d}` — exactly rsmt6a.py. `N` carries **no region**. |
| D8 | ~~Table F layout~~ **SUPERSEDED by D16** | ~~One AIR, two row kinds, segmented join-then-open.~~ The union layout paid join width on every opening and (as built) never range-checked openings — split into **J** (join) and **O** (opening) tables. |
| D9 | ~~Table count~~ **REVISED by D11** | ~~Seven AIRs.~~ **Eight** AIRs (A, J, O, B, C, I, R, P), still **seven logical buses** — buses are cross-table channels, not per-table. |
| D10 | Cross-language golden vectors | Add a test-only `Sha256RefHasher` implementing rsmt6a.py's exact byte encodings, so Rust and Python produce **byte-identical** roots, proofs, and certificates. Production hashing stays Poseidon2 behind the same `Hasher` trait. |
| **D11** | **Table set (R2)** | Eight AIRs: **A** opcodes/advice/roots; **J** join-only coherence; **O** opening-only canonical region + node hash; **B** Poseidon2; **C** leaf sponge; **I** canonical leaf/opened inputs (replaces D); **R** range table `R10(bits,value)` (replaces E); **P** powers `(k, 2^k)`. Seven logical buses unchanged. |
| **D12** | **Range checks (R2)** | Direct variable-width **radix-1024** decomposition against **Table R** = `{(bits, value) : 0 ≤ bits ≤ 10, 0 ≤ value < 2^bits}` (2047 real rows, pad to 2048). `x < 2^k` ⇒ digits `x = x0 + 2^10 x1 + 2^20 x2`, `k = 10h + s`, one-hot `u[3]` picks `h`; digits `< h` looked up `(10, xi)`, digit `h` looked up `(s, x*)`, digits `> h` forced zero. **No complement, no wide multiply.** Subsumes the byte range (a byte = `(8, value)`), so Table E is deleted. |
| **D13** | **Coherence via R2** | Per join: shared prefix `H`, child tails `L_l, L_r`; `r = 10 h_r + s_r`, `k = W−r−1 = 10 h_k + s_k`, `pow_b = 2^k` (**one** Table-P lookup; `pow_a = 2·pow_b` derived). `p[q] = 2·pow_b·H`; `ρ_l[q] = p[q] + L_l`; `ρ_r[q] = p[q] + pow_b + L_r`. Range: `H < 2^r`, `L_l < 2^k`, `L_r < 2^k` (gated), `δ−d−1 < 2^8`. Since `r+k+1 = W ≤ 30`, all terms `< 2^W < ORDER`, so field equations are integer equations and the side bit is uniquely forced. **`hi_l = hi_r = H`, `β_l = 0`, `β_r = 1` are shared/constant — not witnessed.** |
| **D14** | **Derived, not witnessed (R2)** | `gap = δ−d−1`, case bits `b00/b01/b10/b11` (degree-2 products of the two `none` bits), and `right_ptr = parent_idx−1` are **expressions**, not columns. Only `pow_b` is looked up (not `pow_a`, not `2^r`). |
| **D15** | **Canonical inputs (R2)** | Table **I** stores only radix-1024 digits of every leaf key/value (8 wide limbs × 3 digits + 1 tail limb × 2 digits = 26 digits each, 52/leaf), range-checked via R; the 18 hash limbs are **linear expressions** of the digits, sent to C. Table **O** stores 26 region digits and reconstructs its 9 region limbs. This proves every private leaf/opening input has a genuine 256-bit byte encoding (closes the finding-5 faithfulness gap). J regions are then canonical by induction (prefix copied from an advised child + boundary `< 2^W` + lower limbs zero). |
| **D16** | **Split J / O (R2)** | Separate join and opening AIRs. J receives Bus 1 children, runs coherence; O runs full canonical-region + node hash. Avoids paying join width on openings and lets case bits be derived expressions without extra kind-gating degree. |
| **D17** | **Poseidon2 tagged projection (R2) — IMPLEMENTED as a two-bus split** | Goal: terminal permutations expose only their digest so receivers carry no 8-limb output tail. The masked-tuple form `(mode, input[16], output[0..8], mode·output[8..16])` was **rejected**: `mode·output` is degree 2 and this batch-stark requires degree-1 LogUp tuple elements (→ `OodEvaluationMismatch`); making `mode` preprocessed doesn't help (the product is still degree 2). **Built instead as two buses:** `p2ff` = full `(input[16], output[16])` for feed-forward perms; `p2term` = `(input[16], output[0..8])` for terminal perms. B tags each arena entry `mode`, emits `(ff_mask, term_mask)` preprocessed (each degree 1), and **double-sends** (one lookup per bus, exactly one mask set). Receivers pick their bus. Every tuple and multiplicity is degree 1. Table F keeps only `mid[16]` (feed-forward prefix); the children-block digest rides in `parent_new`/`parent_old`, which the `p2term` receive binds to the real Poseidon2 output. |
| **D18** | **No global permutation dedup (R2)** | One Table-B request per *logical* evaluation; share only the intentional node prefix **within a join** (one send, one receive, used locally for both children blocks). Global dedup would require sender multiplicity > 1, which B's per-lane mult-1 send cannot express. Net B growth is negligible (coincident inputs ⇒ duplicate keys ⇒ rejected). |
| **D19** | **Post-order via `subtree_start` (R2)** | Replace `left_ptr/right_ptr` with a `subtree_start` value on Bus 1. Base opcode: `start = row_idx`. Join: `right_root = parent_idx−1`, `left_root = right.start−1`, `parent.start = left.start`. Final row: `start = 0`. Proves contiguous post-order subtrees algebraically — rules out forward edges and disjoint cycles, **removing the Poseidon fixed-point / functional-graph assumption** (README §"Functional-graph corner") and the pointer range-check hardening. |
| **D20** | **Public `old_root_is_none` (R2)** | Table A exposes **17** public values: `old_root[8]`, `new_root[8]`, and `old_root_is_none`. Distinguishes genesis `None` from `Some([0;8])` in the statement (closes the finding-6b gap). |

Each decision gets a short doc-comment at its definition site referencing this
table.

---

## 0.5 Design revision R2 (post-review) — supersedes the M3/M4 table & bus design

A design review after the first M4 wiring found the original arithmetization
sound-in-principle but **not optimal and with two real gaps**. R2 (decisions
D11–D20 above) revises the table architecture, range machinery, input encoding,
and post-order proof. This section records the findings, the response, and the
migration status. **Implementation is paused at the end of M4 Bus 7 until the
revised tables land.**

### Findings and disposition

1. **142-col Table F budget was misleading.** F still owed `mid[16]` + terminal
   sponge outputs for Bus 2 → ~174 under the full-output design. → **D17**
   (tagged projection: only `mid[16]`) + **D16** (split J/O) bring join width to
   ~128.
2. **Range scheme was lookup-heavy** — a 2-child join needed ~45 LogUp aux
   columns (42 byte + 3 power receives). → **D12/D13** (R10 direct
   decomposition): ~14 range + **1** power receive, ~15 aux columns.
3. **Redundant witness** (`hi_l=hi_r`, constant `β`, `gap`, `pow_a`, case bits,
   `right_ptr`). → **D13/D14** make them shared/constant/derived.
4. **Openings were never actually range-checked** — the union layout zeroed all
   range/power columns on opening rows. → **D16** (dedicated O table with real
   canonical-region checks).
5. **Input encoding underconstrained (soundness/faithfulness bug).** Table D
   accepted field-valued limbs with no 30/16-bit canonicality; the AIR proved
   ∃ *field-limb* preimages, not ∃ *byte-encoded* keys/values the CPU semantics
   accept. → **D15** (Table I: range-checked radix-1024 digits; limbs are linear
   expressions).
6. **Two avoidable assumptions.** (a) Functional-graph cycle corner → **D19**
   (`subtree_start` proves contiguous post-order, no Poseidon fixed-point
   assumption). (b) `old_root_is_none` not public → **D20** (17 public values).

The **complement lemma** built in the paused M4 work (`docs/coherence-range.md`,
the F `*_bytes`/`pow_r` columns and their constraints) is **correct but
superseded**; keep it in-tree as a documented fallback, do **not** finish its
Bus-5 wiring.

### Revised coherence cost (per 2-advised-child join)

| | complement (old) | R10 (D13) |
|---|---:|---:|
| decomposition columns | 32 (`*_bytes`) | 9 (`H[3], L_l[3], L_r[3]`) |
| selector/offset columns | `pow_r` + scalars | 8 (`u_r[3], s_r, u_k[3], s_k`) |
| Bus-5/R range receives | 42 | ~14 |
| Bus-7 power receives | 3 | 1 (`pow_b`) |

All constraints stay **degree ≤ 3**: two linear lookup inputs per LogUp aux
column (degree 3); the selected boundary digit `x* = Σ u_i x_i` is degree 2 and
gets its own lookup; `has·(ρ − 2·pow_b·H − tail)` is degree 3.

### Estimated widths (pre-exact-indexing)

- **J** ~128 main cols (incl. `mid[16]` and `subtree_start` post-order columns).
- **O** ~85 main cols (26 region digits + `mid[16]` + node-hash columns).
- **I** ~52 digit cols/leaf + range machinery; limbs are expressions.
- **R** = `R10`, 2048 rows, `(bits, value)` preprocessed + `mult`.

### Migration status — R2 substantially implemented (all 7 buses proving)

**★ The complete R2 arithmetization proves & verifies end-to-end** through
`prove_batch`/`verify_batch`: 8 tables (A, B, C, D, R, F, P — D still stands in
for I), **all seven LogUp buses balanced** (tree, p2, parent, leaf, range [=u8
subsumed by R10], batch, pow2), the R10 coherence digit-sound, public
`old_root_is_none`, every digest bound to a real Poseidon2. **Both remaining
soundness gaps are now closed:** (#5) input-limb canonicality — DONE via Table D
digit range-checks (`key_d`/`value_d` radix-1024 digits, reconstruction gated by
`is_real`, 52 range-bus receives/row); (#6a) `subtree_start` (D19) — DONE: Bus 1
now carries `subtree_start`, joins derive both child rows (`right = parent−1`,
`left = rs−1`) and inherit the left child's start, the root's start is 0, so
contiguous post-order is proved algebraically — **the Poseidon fixed-point /
functional-graph assumption is removed** (no more free `left_ptr`, no locality
column). **Width opt DONE (D17 tagged Bus 2):** realized as a **two-bus split**
(`p2ff` feed-forward full + `p2term` terminal digest) rather than a masked tail
(`mode·output` is degree 2 → `OodEvaluationMismatch`; the batch-stark needs
degree-1 tuple elements). Table B tags each perm and double-sends under two
preprocessed masks; **Table F is now 142 cols** (dropped `new_out`/`old_out` — the
children-block digest rides in `parent_new`/`parent_old`, which the terminal-bus
receive binds to the real Poseidon2 output, also closing a latent
`parent_new`/`parent_old` under-constraint). Under the 150 soft budget; the J/O
split is no longer needed for width. **Remaining:** M6 (perf/bench), M7 (spec).

- **M0, M1** (`rsmt-core`, `rsmt-hash`): unaffected — done, green.
- **M2** (`rsmt-witness`): revise per D14/D15/D18/D19 — drop redundant
  `ChildCoh` fields, emit R10 digits + one-hot offsets, emit canonical input
  digits, emit `subtree_start`, stop global arena dedup. Self-validation and
  invariants extend accordingly.
- **M3** (`rsmt-air`): **A** gains public `old_root_is_none` + `subtree_start`
  (drop `left_ptr/right_ptr`); **F → J + O** rewrite per D12/D13/D16; **E → R**
  (R10); **D → I** (D15); **B** gains the `mode` tag (D17). Degree regression +
  per-family negatives re-derived.
- **M4** (`rsmt-air::dispatch`, `rsmt-prover`): the seven buses re-wired on the
  new layouts. **Kept from the paused work:** the `RsmtAir` enum + `prove_batch`
  round harness, and the validated **one-`register_lookup`-per-tuple** rule.
  Bus 7 now carries **one** `pow_b` receive per join, not three.

---

## M0 — hashing and reference vectors (`rsmt-hash`, new `vectors/`)

Rewrite `rsmt-hash`:

- [ ] `leaf_hash` unchanged except key limbing per D1/D2 (verify the current
      rate-addition pattern for steps 1–2 still matches the spec; keep the
      per-step input layout table in the module docs).
- [ ] New `node_prefix_block(d, region_limbs) -> State` and
      `node_children_block(mid, left, right) -> State`; `node_hash` composed
      from both; delete the single-permutation `node_hash_input`.
- [ ] `region_limbs(key_limbs, d) -> [u32; 9]` (mask below bit `d`) plus the
      boundary-limb split helper `split_limb(limb, W, r) -> (hi, beta, lo)` —
      shared later by tree, witness generator, and tests.
- [ ] Unit tests: determinism, digest changes on every input field (d, each
      region limb, each child limb), prefix-block sharing equals recomputation.

Reference vectors:

- [ ] `vectors/gen_vectors.py` — imports `rsmt6a.py`, runs N seeded multi-round
      scenarios (mixed batch sizes, splits at leaf and junction edges, deep
      shared prefixes, genesis, single leaf), dumps JSON: batches, opcode
      streams with operands, roots per round, inclusion certs, non-inclusion
      chains.
- [ ] Rust test (feature `sha-ref`): replay every vector through
      `Sha256RefHasher` — roots, streams, and certs byte-identical.

**Exit criteria:** vector suite green; Poseidon2 node sponge unit-tested;
no other crate compiles yet against the new API (expected — they are rewritten
in M1/M2).

## M1 — reference core (`rsmt-core`)

Rewrite tree + verifier to rsmt6a semantics; this crate is the **differential
oracle** for everything after it, so it gets the heaviest property testing.

- [ ] `tree.rs`: nodes store absolute `(depth: u16, region: [u32; 9])`;
      `batch_insert(batch) -> (applied, Vec<Op>)` ports rsmt6a.py
      `_insert / _split_edge / _build / _emit_preserved` (including: opened
      forms only under new junctions; frozen-leaf merge emits `OL`; dedup of
      already-present keys).
- [ ] `proof.rs`: `Op` enum per D7; `verify_consistency` is the compact
      verifier — advice stack `(old, new, Option<(delta, rho)>)`, region
      derivation with agreement, coherence (`delta > d`, side bit), the
      ≥1-advised and both-advised-when-new rules, four-way algebra, strict
      batch ordering, exhaustion checks. Return typed errors distinguishing
      every rejection reason (the AIR tests will assert on them).
- [ ] `certs.rs`: inclusion certificate (bitmap + siblings; verifier derives
      regions from the key) and non-inclusion chain (openings along the
      key-directed descent).
- [ ] Tests:
      - replay the M0 vectors with `Sha256RefHasher` **and** the same
        scenarios with the Poseidon2 hasher (structure equal, digests differ);
      - port rsmt6a.py's self-tests: honest multi-round history, the
        shadow-insertion stream rejected in both opaque-`S` and opened forms,
        re-recording rejected at several depths, canonical junction depth
        forced (`d ± 1` rejected), tamper set (dropped/duplicated batch item,
        depth shift, region bit flip, value change);
      - proptest: random rounds → verify; random single mutations of stream /
        operands / batch → reject.

**Exit criteria:** differential parity with rsmt6a.py; all attack vectors
rejected with the expected error; `cargo test -p rsmt-core` < 30 s.

## M2 — out-of-circuit preprocessing (`rsmt-witness`)

> **⚠ R2 (§0.5):** the `TracePlan` shape below is the *original* design. Revised
> per D14/D15/D18/D19: drop redundant `ChildCoh` fields (`gap`, `pow_a`, `pow_r`,
> the complement `*_bytes`, constant `β`); emit **R10 digits + one-hot
> offsets** for `H/L_l/L_r` and the canonical **input digits** (Table I);
> emit **`subtree_start`** instead of `left_ptr/right_ptr`; **stop global arena
> dedup** (one B request per logical eval, prefix shared only within a join).

All data-dependent computation happens **here, before trace generation**, so
that trace fill is a parallel copy and the AIR never needs data-dependent
control flow. New module `plan.rs` produces a `TracePlan`:

```
TracePlan {
  publics:  { old_root[8], new_root[8] },
  shape:    { n_ops, n_join, n_open, n_l, n_ol, n_batch, n_perms },   // public
  a_rows:   Vec<ARow>,      // opcode, digests, advice, ptrs, batch/opened idx
  f_rows:   Vec<FRow>,      // join: children+advice+p+q/r+hi/lo+case bits+mid states
                            // open: d', p', c_l, c_r, mid state, digest+tail
  c_rows:   Vec<CRow>,      // 3 per leaf, kind = batch|opened, full sponge states
  d_rows:   Vec<DRow>,      // sorted batch limbs
  perms:    Vec<[F; 16]>,   // deduplicated permutation inputs (arena)
  e_mults:  [u32; 256],     // byte-range multiplicities
  p_mults:  [u32; 31],      // pow2 multiplicities
}
```

Work items:

- [ ] Single walk of the opcode stream computing, per row: post-order
      pointers (`left_ptr`, `right_ptr = idx − 1`), case bits, derived region,
      the one-hot boundary-limb selector `q[0..9]` + offset `r` for each
      junction depth (`W = 30` for limbs 0..7, `16` for limb 8), and the
      per-advised-child `(hi, lo)` split with its two pow2 operands — all via
      the shared helpers from M0.
- [ ] **Permutation arena**: every Poseidon2 evaluation (leaf steps, prefix
      blocks, children blocks) computed exactly once, stored as
      `(input, output)`; A/F/C rows reference arena indices; Table B trace is
      the arena chunked 8 lanes/row; prefix blocks are naturally deduplicated
      between old/new digests of one junction.
- [ ] Multiplicity tallies for E (depths, depth gaps, range chunks) and P
      (shift lookups) accumulated during the same walk.
- [ ] Builder-side validation (fail fast, before proving): the plan is
      re-checked against `rsmt-core::verify_consistency`; any mismatch is a
      bug, not a proof failure.
- [ ] Trace fill: `par_iter` row fill per table from the plan; no hashing, no
      big-int math, no allocation in the fill loops. Determinism test: serial
      and parallel fills byte-identical.

**Exit criteria:** for every M1 scenario, plan builds, self-validates, and a
`check_plan_invariants` test asserts internal consistency (pointer discipline,
arena coverage, multiplicity totals equal receiver counts).

## M3 — AIR local constraints (`rsmt-air`)

> **⚠ R2 (§0.5):** table set is now **A, J, O, B, C, I, R, P** (D11). Changes vs.
> the text below: **A** adds public `old_root_is_none` (17 publics, D20) and
> `subtree_start` (drops `left_ptr/right_ptr`, D19); **Table F → J + O** (D16),
> both using **R10** coherence (D12/D13) — J is join-only (shared `H`, constant
> side bits, one `pow_b` lookup, `mid[16]`), O is opening-only (canonical region
> digits + node hash); **Table E → R** (`R10(bits,value)`, D12); **Table D → I**
> (canonical range-checked input digits, D15); **Table B** gains the `mode` tag
> (D17). The `#[repr(C)]`/`cast`/`width_of` pattern and the degree-regression +
> per-family-negative discipline below are **kept**.

Rewrite the table AIRs against the plan structs. Column layouts are defined as
`#[repr(C)]` structs with `Borrow` casts (one source of truth for widths;
export `TABLE_*_WIDTH` from the struct size). Every table lands with
`p3_air::check_constraints` unit tests (fast, no FRI) before any bus exists.

Per-table work, with the constraint families and degree budget:

**Table A** (~37 main cols: 5 selectors, digests 17, advice 11, `batch_idx`,
`left_ptr`, `node_hash_old_needed`, `opened_idx`):
- [ ] one-hot selectors; per-opcode digest shapes (`S/O/OL ⇒ old = new`;
      `L ⇒ old = 0, old_is_none = 1`); per-opcode advice shapes (`S ⇒
      has_advice = 0 ∧ delta = rho = 0`; `L/OL ⇒ delta = 256`); canonical
      zeroing; padding rows zero; boundary rows pin publics. Max degree 2.

**Table F** (union layout join/opening, target ≤ ~150 main cols; preprocessed
`is_join`, `is_open` per D8):
- [ ] join: case-bit algebra (`b01/b10/b11/parent_none` products of none
      bits — keep explicit columns so downstream rules stay degree ≤ 3),
      four-way pass-through, tail zeroing, locality
      `right_ptr = parent_row_idx − 1`;
- [ ] coherence block per child, gated by `has_x`: one-hot `q` (booleanity +
      sum = 1), `d = Σ offset(q) + r`, prefix-limb equalities via running
      indicators `lt_j/gt_j` (linear in `q`), boundary-limb split
      `rho_x[q_limb] = hi·pw_a + beta·pw_b + lo` and `p[q_limb] = hi·pw_a`
      (witness×witness×gate ⇒ **degree 3 — the table's max**; verify with a
      symbolic-degree regression test), `W` as the linear expression
      `30 − 14·q[8]`;
- [ ] scalar rules: `(1−has_l)(1−has_r) = 0`;
      `(1−b11)(2−has_l−has_r) = 0`;
- [ ] opening rows: region canonical-padding sub-block on `(d', p')`, digest
      column layout shared with join parent columns;
- [ ] selector-gated cross-zeroing: join-only columns zero on opening rows
      and vice versa (this is what makes the union layout safe).

**Table C**: kind bit (preprocessed, segmented batch-then-opened per D8
analogue), existing step-0 init / step-transition / continuity constraints
unchanged, opened rows simply skip the Bus 6 receive.

**Table B**: unchanged wrapper around `VectorizedPoseidon2Air` + lane mask;
only the sizing formula changes (`3·(n_l + n_ol) + n_join + n_b11 + n_open +
n_junction_prefixes`).

**Table D**: unchanged (preprocessed batch, shape-only on the verifier side).

**Table E**: unchanged AIR; more receiver classes documented.

**Table P** (new, trivial): 31 preprocessed rows `(r, 2^r)`, witness `mult`.

- [ ] Degree regression test: build each AIR symbolically, assert
      `max_constraint_degree` = the documented value (A:2, F:3, C:2, …), and
      set the `BaseAir::max_constraint_degree` hints accordingly (see
      p3-docs.md §2.3).

**Exit criteria:** every table passes `check_constraints` on plan-generated
traces for all M1 scenarios, and **fails** on a first quick negative set (one
hand-picked violation per constraint family).

## M4 — buses and end-to-end proving (`rsmt-air::dispatch`, `rsmt-prover`)

> **⚠ R2 (§0.5):** **kept** from the paused work — the `RsmtAir` enum, the
> `prove_batch` round harness (`rsmt-prover/round.rs`), and the validated
> **one-`register_lookup`-per-tuple** rule (bundling inputs ⇒
> `OodEvaluationMismatch`). **Re-wire** the seven buses on the R2 layouts:
> Bus 1 carries **`subtree_start`** (D19), Bus 2 is the **tagged** tuple (D17),
> Bus 5 goes to **Table R** as `(bits, value)` (D12), Bus 6 is **I → C** (D15),
> Bus 7 carries **one `pow_b`** receive per join (D13). Re-derive the LogUp
> transition degree with the degree-2 `mode·output` term (D17).

- [ ] Define the seven buses exactly as the README table (tuple layouts are
      `const` slices next to the column structs; a unit test asserts sender
      and receiver tuple lengths match per bus).
- [ ] Multiplicity expressions: sends/receives gated by preprocessed
      real/kind columns wherever possible (degree 1 multiplicities); Bus 2
      old-hash receive gated by `is_join · b11` (degree 2 — check LogUp
      transition degree `1 + max(num, den)` stays within the FRI budget).
- [ ] Aux-column budget: start with one `Lookup` per tuple (the known-good
      pattern, incl. Table B's 8 per-lane lookups); file a measured follow-up
      in M6 for merging tuples that share a bus within one AIR.
- [ ] `RsmtAir` enum: add `P`, update dispatch, shapes, preprocessed
      generation from the public `shape` struct.
- [ ] `rsmt-prover`: replace the demo pipeline with `prove_round(plan) ->
      (Proof, PublicShape)` and `verify_round(proof, publics, shape)`;
      the `PublicShape` (per-table real-row counts) travels with the proof —
      it is part of the statement (fixes all non-D preprocessed traces).
- [ ] End-to-end tests: all M1 scenarios prove + verify under the default FRI
      config; genesis round; large mixed round (prefill + batch) behind
      `#[ignore]` for CI-slow.

**Exit criteria:** honest end-to-end green; a wrong public root fails; a
truncated proof fails; serial/parallel prover outputs byte-identical.

## M5 — adversarial suite (the underconstraint hunt)

This milestone is the point of the project; it ships as `rsmt-prover/src/
tamper.rs` (rewritten) plus a new `sweep.rs`. All tests run at the
`check_constraints`-plus-LogUp-balance level first (fast), with a sampled
subset run through full prove/verify.

- [ ] **Column-sweep harness** (systematic): for each verifying scenario,
      for every table, every main-trace column, perturb one real-row cell by
      `+1` and assert the constraint system or a bus balance breaks. Maintain
      an explicit, reviewed allowlist of intentionally-free cells (Table E/P
      `mult`, don't-care cells zeroed by cross-kind constraints — each with a
      one-line justification). **A new column that survives the sweep without
      an allowlist entry fails CI.** This is the primary defense against
      underconstrained columns.
- [ ] **Bus-sweep**: for every bus, remove one send / duplicate one receive /
      swap two tuple elements between rows — assert imbalance.
- [ ] **Targeted tamper matrix** (from README): child swap; A-row
      duplication; locality break; pass-through break; `old_is_none` forgery;
      digest scramble; Poseidon2 tail tamper; permutation reuse across rows;
      derived-`p` bit flip; advice `rho` flip in transit; `delta ≤ d`;
      out-of-range `hi`/`lo`; broken zero-padding of `p` and of `p'`;
      advice dropped under a new junction (**the shadow-insertion vector,
      end-to-end**); misdirected opening; opened digest consumed by `L`;
      batch digest consumed by `OL`; opening tuple consumed by `N`; one row's
      digest with another row's advice; Table E multiplicity break; Table P
      shift misuse (wrong `r`); unmasked padding lane in B; nonzero padding
      row in each table.
- [ ] **Differential fuzz**: seeded generator produces (a) honest rounds —
      must prove; (b) mutated streams that the CPU verifier rejects — the
      witness builder must refuse *or* the proof must fail; assert no third
      outcome. Run long in nightly CI, short in PR CI.
- [ ] Negative-completeness check: every constraint family and every bus
      appears at least once in the matrix (a coverage table in the test file,
      reviewed manually).

**Exit criteria:** sweep green with a fully-justified allowlist; matrix
green; 10⁴ fuzz cases without a soundness escape.

## M6 — performance

Measured on the new platform; old numbers discarded. Order of work: measure,
then optimize, then re-measure — no speculative tuning.

- [ ] `rsmt-bench` update: `O_ops` and `OL_ops` columns, per-table
      real/padded/width/cells breakdown, prefill sweep, `--hash` selection
      as before. Add a `plan` subcommand timing witness generation alone.
- [ ] Budgets to verify against the README projection: Table B perms =
      `3(L+OL) + 2·new_junctions + 3·b11 + 2·openings` with the prefix-block
      sharing actually realized in the arena (assert in tests); Table B
      growth ≤ ~1.5× the equivalent depth-only workload; Table F width ≤ 150.
- [ ] Optimizations, in expected-value order:
      1. arena + lane packing (no duplicate permutations, no waste lanes);
      2. parallel trace fill and parallel plan walk (independent subtrees);
      3. limb math on `u32`/`u64` throughout the hot path (no BigUint);
      4. aux-column merging for buses sharing an AIR (only if the LogUp aux
         cost shows up in the profile);
      5. revisit `--max-log-arity`, blowup/query trade-offs once cell counts
         are final.
- [ ] Document results in README ("Example results" section, currently
      intentionally empty).

**Exit criteria:** ≥ 10⁴ inserted leaves/s prove throughput on the reference
machine at ~116-bit conjectured soundness, or a written analysis of why not
and what it would take.

## M7 — spec sync and cleanup

- [ ] Rewrite `rsmt-air.md` as the implemented spec: exact column tables
      (generated from the layout structs where possible), constraint lists
      with degrees, bus tuples, preprocessed layouts, prover/verifier API.
- [ ] Delete all remaining legacy: old sort key, old `Op::S(Option)`,
      single-perm node hash, demo binaries superseded by `prove_round`.
- [ ] CI: fmt + clippy (deny warnings), fast test tier (< 2 min), slow tier
      (full prove/verify + fuzz) nightly; vector regeneration job pinned to
      the rsmt6a.py commit hash.
- [ ] Final pass: README cost-projection section replaced by measured data;
      DEVPLAN.md marked done or rolled into issues.

---

## Sequencing and risk register

Dependencies are linear M0 → M4; M5 overlaps M3/M4 (write tamper tests next
to each constraint family as it lands — do not batch them to the end); M6
after M4; M7 last. Suggested checkpoints for review: end of M1 (semantics
locked), end of M3 (constraints locked), end of M5 (soundness case made).

| Risk | Signal | Mitigation |
|---|---|---|
| ~~Table F width blowup~~ **resolved by R2** | — | split into J/O (D16) + R10 (D12) + tagged Bus 2 (D17) → J ~128, O ~85 |
| Constraint degree > 3 on J/O | symbolic-degree test | R2 keeps degree ≤3 (shared `H`, one-hot digit select, `has·(ρ − 2·pow_b·H − tail)`); re-run the regression after the J/O rewrite |
| **LogUp transition degree from tagged Bus 2** (D17) | symbolic degree of the aux column | the `mode·output[8..16]` tuple element is degree 2 → `1 + max(num,den)` may hit 3; verify within the FRI budget, else lift `mode` to a preprocessed column |
| **R10 correctness / coverage** (D12) | negative sweep on out-of-range digits and wrong `(bits,value)` | R must contain every `(bits, value<2^bits)` for `bits ∈ [0,10]`; a golden test enumerates the 2047 rows; sweep tries `value ≥ 2^bits` and asserts rejection |
| **Non-canonical inputs** (D15, finding 5) | sweep sets a key/value limb `≥ 2^30` (or limb-8 `≥ 2^16`) | Table I range-checks every digit; a negative test injects a non-canonical digit and asserts the proof fails |
| Boundary limb 8 (`W = 16`) corner | vector + sweep on depths 240..255 | `W = 30 − 14·q[8]` linear; R10 handles the 16-bit limb as `2` digits (10 + 6); dedicated vectors with splits in the last limb |
| `VectorizedPoseidon2Air` borrow-width assertion | compile-time | keep the lane mask + `mode` in preprocessed/aux, never widen B's core permutation trace |
| Silent completeness gap (honest run unprovable) | differential fuzz case (a) | builder validates plan against the CPU verifier before proving; any refusal on an accepted run is a hard test failure |
| Genesis / empty-batch edge | targeted tests | D6 + **D20** (`old_root_is_none` public): AIR tested with genesis vectors distinguishing `None` from `Some([0;8])` |
| ~~Functional-graph cycle corner~~ **removed by R2** | — | D19 (`subtree_start`) proves contiguous post-order algebraically; no Poseidon fixed-point assumption |
