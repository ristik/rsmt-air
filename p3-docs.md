# Plonky3 — Authoring AIRs for Poseidon2 + Merkle Tree with LogUp Cross-Table Lookups

This guide documents how to design and prove an AIR-based circuit in Plonky3 that
combines a **Poseidon2** permutation table and a **Merkle-tree verification** table,
linked together with a **LogUp** lookup argument. The target field is **BabyBear**
(prime `p = 2^31 − 2^27 + 1`), and the proving stack is `p3-uni-stark` for a single
AIR or `p3-batch-stark` for multiple AIRs sharing one FRI commitment, both built on
`p3-fri`'s `TwoAdicFriPcs`.

The relevant crates:

| Crate | Role |
|---|---|
| `p3-air` | `Air` / `BaseAir` / `AirBuilder` traits, row windows, symbolic constraints |
| `p3-poseidon2` / `p3-poseidon2-air` | Poseidon2 permutation + ready-made AIR |
| `p3-baby-bear` | BabyBear field + Poseidon2 instantiation |
| `p3-merkle-tree` | `MerkleTreeMmcs` (leaf/digest commitment used by FRI) |
| `p3-lookup` | LogUp gadget, `Lookup`, `LookupAir`, `LookupEvaluator` |
| `p3-batch-stark` | Multi-AIR proving with shared FRI commit + global lookups |
| `p3-uni-stark` | Single-AIR STARK pipeline (`prove`, `verify`) |
| `p3-fri` | `TwoAdicFriPcs`, FRI parameters |
| `p3-challenger` | Fiat-Shamir transcript (Duplex Poseidon2 challenger) |

---

## 1. Design rationale

### 1.1 Why two tables?

A Merkle inclusion proof of depth `D` over Poseidon2 hashes requires `D` compressions.
You have two natural ways to encode this in an AIR:

1. **Inline** — embed the full Poseidon2 round structure inside every Merkle row.
   Trace width explodes (Poseidon2 width-16 with optimal S-box registers is ≈ 100s of
   columns) and you pay for it on *every* Merkle row, even rows that aren't actually
   doing a hash.
2. **Tabular + lookup** — keep one *Hash table* (each row = one full Poseidon2
   permutation) and one *Merkle table* (each row = one tree level: holds left/right
   sibling, output digest, plus a small set of control flags). The Merkle table calls
   the Hash table via a lookup whenever it needs the next compression.

Plonky3 strongly favours option (2). Trace columns are scarce and expensive (each
column = one committed polynomial, opened at `zeta` and possibly `zeta_next`), while
LogUp lookups are cheap: one extension-field auxiliary column per lookup and a single
running-sum constraint regardless of how many rows interact.

### 1.2 Why LogUp?

`p3-lookup` ships LogUp (`LogUpGadget`) as the canonical lookup gadget. LogUp turns

```
∏(α − a_i)^{m_i} = ∏(α − b_j)^{m'_j}
```

into

```
∑ m_i / (α − combined(a_i)) = ∑ m'_j / (α − combined(b_j))
```

with `combined(t)` collapsing a tuple `(t_0, …, t_{k−1})` via a Horner fold against
challenge `β`. The advantage over plain permutation arguments: **multiplicities are
explicit**, so a side that "consumes" an element at a multiplicity is automatically
balanced against a producer that emits it once — exactly the Merkle ↔ Hash pattern.

Cost per AIR per lookup: **1 extension column** (the running sum `s`), challenges
`(α, β)` drawn after the main commit, and constraints

- `s[0] = 0`
- `(s[i+1] − s[i]) · D − N = 0` (transition; cyclic in the local-lookup form)
- `s[n−1] + contribution[n−1] = 0` (local) or `= expected_cumulated` (global)

where `D = ∏ (α − combined_j)` and `N = ∑ m_j · ∏_{k≠j}(α − combined_k)` are batched
across all element tuples for that lookup on that row.

### 1.3 Two tables, one bus

We introduce **one global LogUp interaction** named e.g. `"poseidon2"`, with the
schema

```
(input_0, …, input_{W−1}, output_0, …, output_{W−1})
```

where `W = 16` (BabyBear Poseidon2 width). For Merkle compression we typically use
the truncated-permutation pattern: feed `[left_digest ‖ right_digest]` (8+8 elements)
as the first 16-element half of the state and read the first 8 output elements as the
parent digest.

- The **Hash AIR** *sends* one entry per row with multiplicity `1`, exposing the
  permutation's input row (`local.inputs`) and the post-state of the last full round
  (the final `post` array of `local.ending_full_rounds[HALF_FULL_ROUNDS-1]`).
- The **Merkle AIR** *receives* one entry per active compression row with the
  reconstructed input/output of that level, multiplicity `1` gated by an
  `is_compress` flag (degree-1 boolean column).

Because the interaction is global (`Kind::Global("poseidon2".into())`), the prover
records each AIR's local cumulative sum as `LookupData::expected_cumulated`. The
verifier checks `Σ expected_cumulated = 0` across all AIRs in the batch via
`LogUpGadget::verify_global_final_value`. Soundness of the cross-table link reduces to
the LogUp soundness over the random `α, β` drawn after main commitment.

### 1.4 Trace shape — concrete numbers

For BabyBear, the constants exported by `p3-baby-bear` are:

```rust
BABYBEAR_S_BOX_DEGREE                = 7
BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS  = 4
BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16 = 13   // for WIDTH=16
```

With `SBOX_REGISTERS = 1` the Poseidon2 AIR width is roughly:

```
W + HALF_FULL_ROUNDS · 2 · (W · (1+REG) + W)  +  PARTIAL_ROUNDS · ((1+REG) + 1)
```

Pick the row count of the Hash table to be the next power of two `≥ #compressions`,
since both `TwoAdicFriPcs` and the LogUp running-sum prefix scan want power-of-two
heights (`log2_strict_usize(degree)` is asserted in `prove_with_preprocessed`,
prover.rs:44).

The Merkle AIR is a flat trace of all path levels for all proven inclusions, padded
to a power of two with rows whose `is_compress = 0` (so they don't contribute to the
lookup sum).

---

## 2. AIR design — concrete columns and constraints

### 2.1 Hash AIR (Poseidon2)

Reuse `p3_poseidon2_air::Poseidon2Air` directly — it already encodes the
permutation. Its column layout is fixed by `Poseidon2Cols<T, WIDTH, SBOX_DEGREE,
SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>` (see `poseidon2-air/src/columns.rs`).

```rust
use p3_baby_bear::{
    BabyBear, GenericPoseidon2LinearLayersBabyBear,
    BABYBEAR_S_BOX_DEGREE, BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS,
    BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
};
use p3_poseidon2_air::{Poseidon2Air, RoundConstants};

const W: usize       = 16;
const SBOX_REG: usize = 1;
const HF: usize      = BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS;     // 4
const PR: usize      = BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16;    // 13

type HashAir = Poseidon2Air<
    BabyBear, GenericPoseidon2LinearLayersBabyBear,
    W, BABYBEAR_S_BOX_DEGREE, SBOX_REG, HF, PR,
>;

let constants = RoundConstants::from_rng(&mut rng);
let hash_air  = HashAir::new(constants);
```

This AIR's `Air::eval` (`poseidon2-air/src/air.rs:222`) re-runs the permutation
symbolically and asserts equality to each committed `post` register. It already sets
`max_constraint_degree = SBOX_DEGREE` and `main_next_row_columns = vec![]` (single-row
AIR — no `zeta_next` opening for main columns).

To attach the lookup, wrap it. `LookupAir` (lookup_traits.rs) is the extension trait
the batch-STARK prover queries:

```rust
use p3_air::{Air, BaseAir, AirBuilder};
use p3_air::symbolic::{SymbolicExpression, BaseEntry, BaseLeaf, Variable};
use p3_lookup::{Lookup, LookupAir, LookupInput, Kind, Direction};

pub struct WrappedHashAir { inner: HashAir, aux_cols: Vec<usize> }

fn main_var(idx: usize) -> SymbolicExpression<BabyBear> {
    SymbolicExpression::Leaf(BaseLeaf::Variable(Variable {
        index: idx,
        entry: BaseEntry::Main { offset: 0 },
    }))
}

impl LookupAir<BabyBear> for WrappedHashAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        // Allocate one new aux column per lookup (LogUp -> num_aux_cols == 1).
        let next = self.aux_cols.last().copied().map_or(0, |x| x + 1);
        self.aux_cols.push(next);
        vec![next]
    }

    fn get_lookups(&mut self) -> Vec<Lookup<BabyBear>> {
        // Hash AIR sends (inputs, outputs) at multiplicity 1.
        let inputs:  Vec<_> = (0..W).map(main_var).collect();
        // Output columns live at the very end of `Poseidon2Cols`: the `post` slot
        // of the last ending full round. Compute their indices once via
        // `core::mem::offset_of!` or a helper around `Poseidon2Cols`.
        let outputs: Vec<_> = LAST_POST_INDICES.iter().copied().map(main_var).collect();

        let elements = inputs.into_iter().chain(outputs).collect::<Vec<_>>();
        let one      = SymbolicExpression::Constant(BabyBear::ONE);

        let lookup = self.register_lookup(
            Kind::Global("poseidon2".into()),
            &[(elements, one, Direction::Send)],
        );
        vec![lookup]
    }
}

impl<AB: AirBuilder<F = BabyBear>> Air<AB> for WrappedHashAir {
    fn eval(&self, b: &mut AB) { self.inner.eval(b); }
}
impl BaseAir<BabyBear> for WrappedHashAir { /* delegate to inner */ }
```

`AirWithLookups` (blanket-impl in `lookup/src/types.rs:261`) takes care of running
`Air::eval` and then the LogUp evaluator over the registered lookups when the
batch-STARK prover calls `eval_with_lookups`.

### 2.2 Merkle AIR

A minimal column layout, one row per Merkle path level (siblings are written in
"left-first" order — pick a canonical ordering and stick to it):

| group | columns | purpose |
|---|---|---|
| `is_compress` | 1 | boolean: 1 on real compression rows, 0 on padding |
| `is_first`    | 1 | boolean: 1 on the first row of each path |
| `path_bit`    | 1 | boolean: 0 = current digest is left, 1 = right |
| `cur[8]`      | 8 | running digest at this level |
| `sib[8]`      | 8 | sibling digest read from the witness |
| `parent[8]`   | 8 | output digest (= Poseidon2 output truncated to 8) |
| `leaf[8]`     | 8 | only meaningful where `is_first = 1` (boundary input) |
| `root[8]`     | 8 | only meaningful where `is_last = 1` (boundary output) |

Width: 42 columns. All boolean columns get `assert_bool`. Add transition constraints
to chain levels:

```rust
// boundary
b.when_first_row().assert_one(local.is_first);

// transition: if next row is a continuation of the same path, `cur_next == parent`.
let same_path = AB::Expr::ONE - next.is_first;
b.when_transition().when(same_path.clone()).assert_eq(next.cur, local.parent);

// path-bit selects sibling order for the lookup payload.
// Build the 16-wide hash-input expression depending on path_bit:
//   if path_bit = 0:  hash_in = [cur || sib]
//   if path_bit = 1:  hash_in = [sib || cur]
// (Compute by mux: cur*(1-bit) + sib*bit, and the swap.)

// path end: when next.is_first = 1 we are starting a new path,
// so `local.parent == local.root` must hold on that previous row.
b.when_transition().when(next.is_first).assert_eq(local.parent, local.root);
b.when_last_row().assert_eq(local.parent, local.root);
```

The Merkle AIR registers the *receive* side of the bus:

```rust
// Build input as 16-wide vector via the path_bit mux. Multiplicity = is_compress.
let elements: Vec<SymbolicExpression<BabyBear>> = build_hash_input(local).into_iter()
    .chain((0..8).map(|i| main_var(PARENT_OFF + i)))                 // outputs
    .chain((8..16).map(|_| SymbolicExpression::Constant(BabyBear::ZERO))) // pad output to W
    .collect();

let mult = main_var(IS_COMPRESS_OFF);
self.register_lookup(
    Kind::Global("poseidon2".into()),
    &[(elements, mult, Direction::Receive)],
);
```

> **Important:** the *exact* element schema of every AIR registering the same
> `Global("poseidon2")` interaction must match — same arity, same field order. The
> verifier sums `expected_cumulated` across AIRs and rejects if `≠ 0`
> (`LogUpGadget::verify_global_final_value`, logup.rs:325).

### 2.3 Constraint-degree budget

LogUp's transition constraint has degree
`1 + max(deg(num), deg(den))` — see `LogUpGadget::constraint_degree`
(logup.rs:354). With an `element_exprs` of arity 1 (one tuple per row, as we have it)
and degree-1 elements, the LogUp transition has degree 2; with multiplicity column
`is_compress` (degree 1) the numerator stays at degree 2. This is well below
Poseidon2's `SBOX_DEGREE = 7`, so the quotient domain is sized by Poseidon2.

You can hint this to the prover via `BaseAir::max_constraint_degree`:

```rust
fn max_constraint_degree(&self) -> Option<usize> { Some(7) }   // Hash AIR
fn max_constraint_degree(&self) -> Option<usize> { Some(2) }   // Merkle AIR
```

Without the hint, the prover symbolically traverses every constraint to compute it.

---

## 3. Trace generation

### 3.1 Hash trace

```rust
use p3_poseidon2_air::generate_trace_rows;

let inputs: Vec<[BabyBear; W]> = collect_all_compression_inputs(); // truncated perm
let trace_hash = generate_trace_rows::<
    BabyBear, GenericPoseidon2LinearLayersBabyBear,
    W, BABYBEAR_S_BOX_DEGREE, SBOX_REG, HF, PR,
>(inputs, &constants, fri_params.log_blowup);
```

`extra_capacity_bits` must equal `fri_params.log_blowup`; this allocates the
quotient-domain headroom in the trace's backing `Vec` so the LDE doesn't reallocate.
Pad `inputs.len()` to a power of two (any padding rows can be dummy permutations
whose lookup contribution is balanced by extra `Send`/`Receive` if you go
unfiltered — *or* gate the bus with a multiplicity column). Easiest: pad with
zero-input permutations and have the Hash AIR's lookup multiplicity be a real
boolean column `is_active`, set to 0 on padding rows.

### 3.2 Merkle trace

Build a `RowMajorMatrix<BabyBear>` row-by-row from the path witnesses, padding the
row count to a power of two with `is_compress = 0` rows. Make the trace height
**at least as large as the Hash trace's height** if you can — a batch-STARK proof
over `instances` of mixed degree pays for the largest one anyway, so unequal heights
are fine, but the LogUp running sum scales with each AIR's own height.

---

## 4. STARK proving — the full pipeline

Two pipelines depending on whether you keep the AIRs separate (`batch-stark`) or
fuse them into one giant AIR (`uni-stark`). For cross-table LogUp you need
`batch-stark`.

### 4.1 BabyBear FRI / Poseidon2 PCS skeleton

```rust
use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16,
                   default_babybear_poseidon2_24};
use p3_field::extension::BinomialExtensionField;
use p3_challenger::DuplexChallenger;
use p3_fri::{TwoAdicFriPcs, create_benchmark_fri_params_high_arity};
use p3_commit::ExtensionMmcs;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use p3_dft::Radix2DitParallel;

type F   = BabyBear;
type EF  = BinomialExtensionField<F, 4>;          // BabyBear quartic extension
type Perm16 = Poseidon2BabyBear<16>;
type Perm24 = Poseidon2BabyBear<24>;
type Hash    = PaddingFreeSponge<Perm24, 24, 16, 8>;
type Compress = TruncatedPermutation<Perm16, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<<F as p3_field::Field>::Packing,
                              <F as p3_field::Field>::Packing,
                              Hash, Compress, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<F, EF, ValMmcs>;
type Dft = Radix2DitParallel<F>;
type Pcs = TwoAdicFriPcs<F, Dft, ValMmcs, ChallengeMmcs>;
type Challenger = DuplexChallenger<F, Perm24, 24, 16>;
type Config = StarkConfig<Pcs, EF, Challenger>;

// Build the PCS (cap_height = 3 is the Plonky3 example default).
let perm16 = default_babybear_poseidon2_16();
let perm24 = default_babybear_poseidon2_24();
let val_mmcs       = ValMmcs::new(Hash::new(perm24.clone()),
                                  Compress::new(perm16.clone()), 3);
let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
let fri_params     = create_benchmark_fri_params_high_arity(challenge_mmcs);
// fri_params: log_blowup = 1, num_queries = 100  (≈100-bit security w/ PoW).

let pcs       = Pcs::new(Dft::default(), val_mmcs, fri_params);
let challenger = Challenger::new(perm24);
let config     = Config::new(pcs, challenger);
```

`fri_params.log_blowup` is the `extra_capacity_bits` argument to
`generate_trace_rows`. Tune `num_queries` and `query_proof_of_work_bits` for security
(the helpers in `fri/src/config.rs` are presets; for production set them yourself —
`100` queries × `log_blowup=1` ≈ 100-bit conjectured soundness *without* PoW grinding).

### 4.2 Single AIR — `p3-uni-stark`

If you only have one AIR (no cross-table lookups), this is the thinnest path:

```rust
use p3_uni_stark::{prove, verify};

let proof = prove(&config, &air, trace, &public_values);
verify(&config, &air, &proof, &public_values)?;
```

`prove` requires `A: Air<SymbolicAirBuilder<Val<SC>>> + for<'a> Air<ProverConstraintFolder<'a, SC>>`
(prover.rs:392). In debug builds it also asserts `Air<DebugConstraintBuilder<…>>` and
runs `check_constraints` (prover.rs:40), which evaluates the AIR row-by-row over the
real trace and panics on the first non-zero constraint — invaluable while iterating.

### 4.3 Two AIRs + LogUp — `p3-batch-stark`

```rust
use p3_batch_stark::{StarkInstance, ProverData, prove_batch, verify_batch};

let hash_inst = StarkInstance {
    air: &hash_air,                // WrappedHashAir
    trace: &trace_hash,
    public_values: vec![],
    lookups: hash_air.get_lookups_clone(),  // your cached Vec<Lookup<F>>
};
let merkle_inst = StarkInstance {
    air: &merkle_air,
    trace: &trace_merkle,
    public_values: vec![],
    lookups: merkle_air.get_lookups_clone(),
};

let instances = vec![hash_inst, merkle_inst];

// Builds the global preprocessed commitment (none here) and stores `lookups`
// per instance inside `CommonData`.
let prover_data = ProverData::from_instances(&config, &instances);
let common      = &prover_data.common;

let proof = prove_batch(&config, &instances, &prover_data);

verify_batch(
    &config,
    &[hash_air.clone(), merkle_air.clone()],
    &proof,
    &[vec![], vec![]],
    common,
)?;
```

Inside `prove_batch` (batch-stark/src/prover.rs):

1. Each instance's main trace is committed with `Pcs::commit` into one shared
   `TwoAdicFriPcs` commitment.
2. After observing the main commitment, the challenger samples
   `(α_k, β_k)` per lookup `k` (`get_perm_challenges`, `LogUpGadget::num_challenges = 2`).
3. `LogUpGadget::generate_permutation` builds the per-lookup auxiliary trace —
   one extension column per lookup, the running prefix sum of the per-row LogUp
   contributions (logup.rs:386). Globals also receive their `expected_cumulated`
   value here.
4. The aux traces are committed (one extension-field commitment).
5. The challenger samples the constraint-batching `α_constraint`; the prover
   produces quotient values via `quotient_values` (uni-stark/src/prover.rs:400) over
   the Vanishing-times-quotient domain sized by the max constraint degree.
6. Quotient chunks are committed; the challenger samples `zeta`; the PCS opens
   main, preprocessed, permutation and quotient at `zeta` (and `zeta_next` where
   the AIR declared `main_next_row_columns`).
7. FRI low-degree-tests the batched openings.

Verification mirrors steps (1)–(7), and additionally calls
`LogUpGadget::verify_global_final_value(all_expected_cumulated)` which asserts the
sum across instances is zero — the cross-table soundness check.

### 4.4 Soundness summary

- **Per-AIR algebraic consistency**: Poseidon2 round equations hold on every
  Hash row; Merkle path-chaining holds on every Merkle row → enforced by `Air::eval`
  + FRI low-degree test of the quotient.
- **Cross-table linkage**: every Merkle compression has a matching Poseidon2 row →
  enforced by `∑ (Hash sends) − ∑ (Merkle receives) = 0` in extension field, via
  LogUp running sum + global cumulative check. Soundness error per lookup is
  `(N_total / |EF|)` for the Schwartz-Zippel step over `α`, and additionally
  `arity / |EF|` for the `β` collapse — negligible in `EF = BabyBear^4`.

---

## 5. End-to-end checklist

1. Pick `(W=16, SBOX_DEGREE=7, SBOX_REG=1, HF=4, PR=13)` for BabyBear.
2. Sample `RoundConstants` once from a deterministic seed; share the seed
   between prover and verifier (or hash it into the challenger).
3. Define `WrappedHashAir` (sends) and `MerkleAir` (receives) with **identical**
   element schemas under `Kind::Global("poseidon2".into())`.
4. Set `max_constraint_degree` and (optionally) `num_constraints` hints to skip
   symbolic counting.
5. Generate traces with `extra_capacity_bits = fri_params.log_blowup`. Pad row
   counts to powers of two; gate the lookup with a boolean `is_active` /
   `is_compress` multiplicity column on padding rows.
6. Build `Config = StarkConfig<TwoAdicFriPcs<…>, EF, DuplexChallenger<…>>` exactly
   as in `examples/src/types.rs:54`.
7. Wrap each `(air, trace)` in a `StarkInstance` and call
   `prove_batch` / `verify_batch`.
8. In dev, build with `debug_assertions` enabled — `check_constraints` will catch
   off-by-one column indices, missing booleanity, and lookup schema mismatches at
   row granularity before FRI runs.

---

## 6. Pointers to the source

- `air/src/air.rs` — `Air`, `AirBuilder`, `BaseAir`, `RowWindow`, `FilteredAirBuilder`.
- `lookup/src/types.rs` — `Lookup`, `LookupInput`, `Direction`, `Kind`, `LookupAir`,
  `AirWithLookups`.
- `lookup/src/logup.rs` — `LogUpGadget`: `eval_local_lookup`, `eval_global_update`,
  `generate_permutation` (parallel prefix-sum), `constraint_degree`.
- `poseidon2-air/src/{air.rs,columns.rs,generation.rs}` — `Poseidon2Air`,
  `Poseidon2Cols`, `generate_trace_rows`.
- `uni-stark/src/{prover.rs,verifier.rs,config.rs}` — `prove`, `verify`,
  `StarkConfig`, `StarkGenericConfig`.
- `batch-stark/src/{prover.rs,verifier.rs,common.rs}` — `prove_batch`,
  `verify_batch`, `StarkInstance`, `ProverData`, `CommonData`, `get_perm_challenges`.
- `fri/src/config.rs` — `FriParameters`, `create_benchmark_fri_params*`.
- `examples/src/{airs.rs,proofs.rs,types.rs}` — full working stitching of all of the
  above (Poseidon2 + Keccak + Blake3) over BabyBear / KoalaBear / Mersenne31.
