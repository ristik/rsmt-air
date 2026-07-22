# R3 soundness budget, maximum shape, and no-wrap formulas (M0)

`DEVPLAN-R3.md` M0 deliverables ⑤ (R3-D13 combined calculation) and ⑥ (max shapes
+ per-bus no-wrap). This does **not** rely only on `log_blowup·queries + PoW`.

> **Targets (R3-D13).** ≥ **116** bits for the standalone STARK/FRI component, and
> ≥ **100** bits for the complete false-accept probability after LogUp and all
> union bounds. If the calculation cannot justify this, raise parameters or lower
> the maximum shape.

All error terms below are **conservative upper bounds** (lower bounds on bits).
Where an exact constant depends on the pinned Plonky3 (`rev 4b341cc9`) FRI/LogUp
implementation, it is flagged `[reconcile@M10]`; a conservative `O(1)` stand-in is
used so the derived maximum shape is safe, not optimistic.

## 1. Fixed constants

| Quantity | Value | log₂ |
|---|---|---|
| BabyBear order `p = 2³¹ − 2²⁷ + 1` | 2 013 265 921 | 30.907 |
| Extension `EF = BinomialExtensionField<F,4>`, `|EF| = p⁴` | — | **123.627** |
| Challenger | `DuplexChallenger<F, Perm24, 24, 16>` (capacity 8) | sponge ≈ 123.6 |
| FRI `log_blowup b` | 1 (rate ρ = 2⁻¹) | — |
| FRI `num_queries s` | 100 | — |
| FRI `query_proof_of_work_bits t` | 16 | — |
| FRI `max_log_arity`, `log_final_poly_len` | 3, 0 | — |

Source: `crates/rsmt-prover/src/{config.rs,proof_hash.rs}`.

Shape variables (per round, over all seven AIRs):

```text
N     = max padded table height (LDE-free)          n = log2 N
D_LDE = N · 2^b   (FRI evaluation domain size)
r     ≈ n         (# FRI folding rounds)
H     = total committed base-field columns (batched by FRI)
T     = total LogUp interactions (Σ sends + receives)
w     = max compressed-tuple length (≈ 32, the widest bus)
d_c   = max symbolic constraint degree (≤ 3 now; ≤ 5 after M9 pairing)
airs  = 7
```

## 2. Error decomposition (union bound)

Total false-accept `ε ≤ ε₁ + ε₂ + ε₃ + ε₄ + ε₅`.

### ε₁ — FRI query soundness (the "standalone STARK/FRI" number)

- **Conjectured** (ethSTARK / list-decoding to capacity δ→1−ρ, the regime R3-D4
  adopts): `ε₁ ≈ ρ^s + 2^{-t}` ⇒ **b·s + t = 100 + 16 = 116 bits**.
- **Provable** (unique-decoding radius δ = (1−ρ)/2 = ¼): `(1−δ)^s · 2^{-t} =
  (¾)^{100}·2^{-16} ≈ 2^{-57.5}` — inadequate alone. R3 therefore adopts the
  conjectured regime *explicitly* (as do deployed BabyBear STARKs), and records
  the gap here rather than hiding it. Closing it fully would need s ≈ 240 queries
  at ρ = ½, which M10 may trade against a larger blowup.

`ε₁` meets the ≥116 standalone target **by conjecture**; this is the one place R3
depends on the ethSTARK heuristic, and it is called out in the risk register.

### ε₂ — FRI commit-phase (proximity gap / folding)

By the RS proximity-gap theorem (BCIKS'20) applied to the batched, `r`-round
fold, the probability that a function `δ`-far from the code survives is bounded, in
the list-decoding regime, by `[reconcile@M10]`

```text
ε₂ ≲ C₂ · r · D_LDE / |EF| ,   C₂ = O(1)  (take C₂ = 1 conservatively).
```

### ε₃ — DEEP/OOD sampling and quotient soundness

The out-of-domain point `z ∈ EF` and the quotient identity fail with

```text
ε₃ ≲ (d_c + airs) · N / |EF| .
```

### ε₄ — LogUp soundness

By Schwartz–Zippel on the LogUp rational identity `Σ mᵢ/(α−âᵢ) = Σ 1/(α−b̂ⱼ)`
with tuple compression `x̂ = Σ βᵏ xᵏ`, the identity (if the multisets differ) holds
at random `(α, β)` with probability at most `[reconcile@M10]`

```text
ε₄ ≲ T · w / |EF| .
```

(Conservative: the pinned implementation uses independent `α, β`, which only
improves this. Using `T·w` treats the worst case of one shared challenge.)

### ε₅ — Fiat–Shamir / challenger

The Poseidon2 duplex sponge has capacity 8 field elements ⇒ collision/preimage
resistance ≈ `(8/2)·log₂ p ≈ 123.6` bits; grinding is already counted in `ε₁`.
`ε₅ ≪ ` the other terms and is not binding.

## 3. Bits at the recommended maximum shape

**Frozen maximum shape (current FRI params):** `N_max = 2¹⁶` (65 536 padded rows
per table) and `T_max = 2¹⁷` interactions, `w = 32`, `d_c = 5`, `airs = 7`.

| Term | Formula | Value | Bits |
|---|---|---|---:|
| ε₁ query (conjectured) | `b·s + t` | 2⁻¹¹⁶ | **116** |
| ε₂ commit | `r·D_LDE/|EF|` = 16·2¹⁷/2¹²³·⁶ | 2⁻¹⁰²·⁶ | 102.6 |
| ε₃ deep+quotient | `(d_c+airs)·N/|EF|` = 12·2¹⁶/2¹²³·⁶ | 2⁻¹⁰³·⁹ | 103.9 |
| ε₄ logup | `T·w/|EF|` = 2¹⁷·2⁵/2¹²³·⁶ | 2⁻¹⁰¹·⁶ | 101.6 |
| ε₅ FS | sponge capacity | 2⁻¹²³·⁶ | 123.6 |
| **Union total** | Σ | ≈ 2⁻¹⁰⁰·⁹ | **≥ 100.9** |

Both targets are met: standalone STARK/FRI **116** (conjectured), complete
**100.9**. The **binding algebraic term is ε₄ (LogUp)**; it, not the query count,
caps the shape.

**Sensitivity.** Each doubling of `N` (or `T`) costs ≈ 1 bit on ε₂/ε₃ (or ε₄). At
`N = 2²⁰` the union total falls to ≈ 97 bits — below target — so the max shape is a
hard pre-allocation gate, not advice. M10 may raise it by (a) a degree-5 extension
(`|EF| ≈ 2¹⁵⁴`, +30 bits headroom), (b) more queries, or (c) reconciling `C₂` and
the LogUp challenge count with the pinned Plonky3, which is expected to be more
favorable than these worst-case constants.

## 4. Count identities (checked before allocation)

With `n_leaf = n_L + n_Ol`:

```text
n_ops   = n_S + n_open + n_Ol + n_L + n_join
n_perm  = 3·n_leaf + 2·n_join + n_b11 + 2·n_open        (exact arena length)
n_b11  ≤ n_join
n_batch = n_L                                          (existential; no batch table in R3)
```

The verifier recomputes every padded height from these scalar counts and rejects
any shape whose declared heights, `n_perm`, or `n_b11 ≤ n_join` disagree
(`RoundShape` carries scalar counts only — no `Vec<bool>`).

## 5. Per-bus no-wrap formulas

Multiplicities are BabyBear elements; a per-bus **total** multiplicity that reaches
`p` wraps mod `p` and can forge balance. Each bus's maximum total multiplicity,
computed from the shape, must be `< p = 2³⁰·⁹⁰⁷`:

| Bus | Max total multiplicity `M` | No-wrap condition |
|---|---|---|
| `range` | `52·n_leaf + c_J·n_join + c_O·n_open` (`c_J,c_O ≤ 30`) | `n_leaf < p/52 ≈ 2²⁴·⁶` |
| `pow2` | `≤ 3·n_join + n_open` | trivially `< p` |
| `leaf` | `n_leaf` (mult 1/row) | `< p` |
| `parent` | `n_join + n_open` | `< p` |
| `tree` | `2·n_join` (two children/join) | `< p` |
| `p2ff` | `n_leaf·2 + n_join + n_open` (feed-forward occurrences) | `< p` |
| `p2term`| `n_leaf + n_join + n_b11 + n_open` (terminal occurrences) | `< p` |

At the frozen `N_max = 2¹⁶`, `n_leaf ≤ 2¹⁶ ≪ 2²⁴·⁶`, so no-wrap holds with ≈ 2⁸·⁶
margin on the binding `range` bus. The check is nonetheless enforced pre-allocation
(defense against a shape that inflates one bus), computing the **exact** maximum
contribution of each bus from the shape — not a single informal "reasonable batch
size" assumption (`DEVPLAN-R3.md` §6.2).

## 6. What M10 must reconcile

- exact `C₂` (proximity-gap constant) and folding-round count in pinned p3-fri;
- exact LogUp challenge structure (one vs two independent challenges) in p3-lookup;
- whether a degree-5 extension or more queries buys a larger max shape at lower
  total proving cost.

Until then, the frozen numbers above (`N_max = 2¹⁶`, 116 standalone / 100.9 total)
are the operative security statement.
