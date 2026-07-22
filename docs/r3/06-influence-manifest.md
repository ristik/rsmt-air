# R3 column-influence manifest and S1–S12 map (M8)

`DEVPLAN-R3.md` M8. Every main/preprocessed column of the R3 table set
`A/B/L/J/O/R/P` is classified into one of the six influence classes of
`docs/r3/01-security-model.md` §7, with the local constraint, bus, or extraction
use that gives it influence. Classes:

1. **statement-bearing** (public boundary) · 2. **execution-bearing** (extracted
opcode/digest/advice/key/value/region/edge) · 3. **cryptographic** (Poseidon2
in/out) · 4. **interaction-bearing** (bus element or multiplicity) · 5.
**algebraic helper** (low-degree scaffolding, functionally determined) · 6.
**irrelevant** (deleted).

**No R3 table carries a class-6 column** — the reduced A dropped `batch_idx`,
`opened_idx`, `has_advice`, and `node_hash_old_needed`; L/J/O were designed
without dead cells. Padding cells are not a class: they are forced zero by each
table's padding-hygiene constraint (`not_real · cell = 0`).

## Table A (reduced, `table_ar.rs`, width 33)

| Column(s) | Class | Influence |
|---|---|---|
| `is_s,is_o,is_ol,is_l,is_n` | 2, 4 | one-hot opcode (S1); gate every bus mult |
| `old[8]` | 1, 2, 4 | last-row public boundary (S1); parent/tree bus |
| `new[8]` | 1, 2, 4 | last-row public boundary; leaf/parent/tree bus |
| `old_is_none` | 1, 2 | public genesis-vs-`Some([0;8])` (S1); digest-zero rule |
| `delta` | 2, 4 | extracted depth; parent/tree bus |
| `rho[9]` | 2, 4 | extracted region/key; leaf/parent/tree bus |
| `subtree_start` | 2, 4 | post-order edge (S2); tree/parent bus |
| prep `row_idx` | 4 | leaf/parent/tree bus key |
| prep `is_real,is_last_real` | 4, 5 | realness / boundary selector |

## Table L (`table_l.rs`, width 93)

| Column(s) | Class | Influence |
|---|---|---|
| `a_row_idx` | 4 | leaf-bus key (binds to A) |
| `key_digits[26]` | 2, 4 | reconstruct `Key32` (S4); 26 range receives + leaf/p2 bus |
| `value_digits[26]` | 2, 4 | reconstruct `Value32` (S4); 26 range receives + p2 bus |
| `mid_0[16],mid_1[16]` | 3, 4 | leaf-sponge continuation; p2ff receives |
| `digest[8]` | 3, 4 | leaf digest; p2term receive + leaf send |
| prep `is_real` | 4, 5 | realness / bus gate |

Every L column is bus-driven; the only local rule is padding hygiene. S4 holds
because each digit is range-checked to its fixed width, making the limb
reconstruction injective.

## Table J (`table_j.rs`, width 142)

| Column group | Class | Influence |
|---|---|---|
| `parent_row_idx,ls,rs` | 2, 4 | post-order edges (S2); tree/parent bus keys |
| `depth,region[9]` | 2, 4 | junction position; p2ff + parent bus + range |
| `q[9],r_off,pow_b,h,h_d,u_r,s_r,u_k,s_k` | 5, 4 | R10 coherence scaffolding (S6); range/pow2 bus |
| `width_r[3],width_k[3]` | 5, 4 | materialized widths keep range tuple degree 1 |
| `l_*/r_* (old,new,none,has,delta,rho,l,l_d)` | 2, 4 | child state + coherence (S6/S7); tree/p2 bus |
| `b01,b10,b11,parent_none` | 2, 5 | four-way case bits (S7) |
| `parent_old[8],parent_new[8]` | 2, 3, 4 | node digests; p2term + parent bus |
| `mid[16]` | 3, 4 | shared node prefix; p2ff receive |
| prep `is_real` | 4, 5 | realness / bus gate |

## Table O (`table_o.rs`, width 89)

| Column group | Class | Influence |
|---|---|---|
| `a_row_idx,depth` | 2, 4 | opening position; parent bus |
| `region_digits[26]` | 2, 4 | canonical region (S5); 26 range receives + p2ff + parent |
| `q[9],r_off,pow_b,h_digits,h_u,h_s,width_h` | 5, 4 | boundary scaffolding (S5); range/pow2 bus |
| `left_digest[8],right_digest[8]` | 2, 3, 4 | opened children; p2term input |
| `prefix_mid[16]` | 3, 4 | node prefix; p2ff receive |
| `digest[8]` | 3, 4 | node digest; p2term receive + parent send |
| prep `is_real` | 4, 5 | realness / bus gate |

## Tables B / R / P

- **B** (`VectorizedPoseidon2Air`): the entire permutation trace is class 3
  (cryptographic) and class 4 (p2ff/p2term sends). Preprocessed ff/term masks are
  class 4 (derived from the scalar `(n_ff, n_term)` — no `Vec<bool>`).
- **R** (`table_r.rs`): fixed `(bits,value)` preprocessing is class 4; the single
  `mult` main column is class 4 — locally free, globally fixed by range balance
  (S9). Padding rows have fixed tuples and zero effective multiplicity.
- **P** (`table_p.rs`): `(k,2^k)` preprocessing class 4; `mult` class 4, fixed by
  pow2 balance (S9).

## Soundness-lemma → code map (S1–S12)

| Lemma | Where enforced | Test |
|---|---|---|
| **S1** opcode partition | `table_ar` one-hot + `old_is_none`/digest rules | `table_ar/tests` |
| **S2** post-order topology | `subtree_start` chain + tree-bus in-degree; `build_r3_plan` D19 checks | `r3build/tests` (Lemma B), `r3round/tamper` (subtree_start) |
| **S3** advice/digest co-binding | one tuple per child on tree/parent bus, keyed by row index | `r3round` balance |
| **S4** leaf byte-faithfulness | L digit range + injective reconstruction | `r3plan/tests` (digits reconstruct), `r3round/tamper` (l_digest) |
| **S5** opened-region faithfulness | O boundary constraints + region digit range | `r3plan/tests` (256 depths), `table_o/tests`, `r3round/tamper` (o_region) |
| **S6** join coherence | J R10 boundary equations | `r3plan/tests` (coherence), `table_j/tests`, `r3round/tamper` (j_coherence) |
| **S7** four-way old state | J case bits + passthrough/hash | `r3plan/tests` (four-way), `table_j/tests` |
| **S8** permutation occurrence balance | occurrence arena (no dedup) + p2 buses | `r3arena/tests` (mult-2 regression), `r3round` balance |
| **S9** range/power integrity | R/P balance + `build_r3_plan` no-wrap gate | `r3round/tamper` (range_mult, pow2_mult), `shape.validate` |
| **S10** verifier independence | reduced A + `rsmt-protocol` (no seed/FRI in envelope) | `rsmt-protocol/tests` |
| **S11** transcript binding | `statement_bytes` domain separation (absorption into challenger: M7 tail) | `rsmt-protocol/tests` (domain-sep) |
| **S12** extraction theorem | `build_r3_plan` (verified stream → A/L/J/O) + this manifest | `r3build/tests`; paper note pending |

**Open items** (refinement, not soundness): S11's transcript *absorption* into the
challenger and the true verifier-owned preprocessing split are the M7 tail; S12's
written paper proof composes this manifest with `docs/r3/02`/`03`.
