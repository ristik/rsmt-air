# Pre-R3 baseline: benchmarks, goldens, API status (M0)

`DEVPLAN-R3.md` M0 deliverables ⑦ (benchmarks), ⑧ (golden roots/streams), ⑨
(mark combined API experimental). This is a **moving record**, updated as R3
milestones land; the security statements in `01`–`04` are the frozen part.

Captured at commit `rsmt6a 1st cut (insecure)` (`4acc870`), pre-R3, on the dev
machine (`darwin 24.6.0`), `--release`, `poseidon2` proof hash, FRI
`log_blowup=1 num_queries=100 query_pow=16 max_log_arity=3` (~116 conjectured
bits). Numbers are single-run, not warmed medians — M0 captures orders of
magnitude; M8/M10 add the pinned-machine, warmed, dispersion-reported corpus
required by `DEVPLAN-R3.md` §8.2.

## 1. Batch-size sweep (prefill 1024)

Command: `rsmt-bench perf --batches 1,16,64,256,1024 --prefill 1024 --hash poseidon2`

| batch | L | N | B perms | total cells | max main W | witness ms | prove ms | verify ms | proof KB |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 10 | 35 | 31 722 | 2384 | 0 | 67 | 68 | 1830 |
| 16 | 16 | 104 | 389 | 199 184 | 2384 | 1 | 85 | 76 | 1867 |
| 64 | 64 | 298 | 1 200 | 771 776 | 2384 | 3 | 130 | 76 | 1894 |
| 256 | 256 | 741 | 3 319 | 1 602 944 | 2384 | 10 | 185 | 75 | 1884 |
| 1024 | 1024 | 1 787 | 8 823 | 5 926 016 | 2384 | 27 | 548 | 79 | 1966 |

Observations that inform R3 optimization order (§8.4):

- **Table B dominates** every shape: `max main width = 2384` is the vectorized
  Poseidon2 permutation trace (8 lanes), independent of batch. This is the
  inherent hash cost R3 cannot remove (it can only batch/represent it more
  cheaply — B width is an M10 S-box/vector-length question, not an AIR-table
  redesign).
- **Cells scale ≈ linearly** with batch; proof size is nearly flat (~1.9 MB,
  dominated by fixed FRI overhead at these heights).
- **verify ≈ 76 ms flat**; prove grows with batch. R3's dominant-table work is L
  and J/O width, not verify time.

## 2. Per-table breakdown (batch 64, prefill 1024)

Command: `rsmt-bench round --batch 64 --prefill 1024 --hash poseidon2`

| Table | real | padded | main | prep | cells |
|---|---:|---:|---:|---:|---:|
| A | 597 | 1024 | 37 | 3 | 40 960 |
| B | 1200 | 256 | 2384 | 16 | 614 400 |
| C | 342 | 512 | 50 | 7 | 29 184 |
| **D** | 64 | 64 | **1** | **72** | 4 672 |
| R | 2047 | 2048 | 1 | 3 | 8 192 |
| **F** | 312 | 512 | **142** | 3 | 74 240 |
| P | 31 | 32 | 1 | 3 | 128 |

`total cells = 771 776`, `max_main_width = 2384`, `proof = 1894 KB`,
`trace = 2.1 ms`, `prove = 138 ms`, `verify = 76 ms`.

This snapshot is the "before" side of the R3 layout claims (`DEVPLAN-R3.md` §5.1):

- **D** carries **72 preprocessed columns** and **1 dummy main** — the batch and
  its canonical digits live in preprocessing / the shared commitment. This is the
  finding-§4 trust-boundary defect R3 eliminates (batch → L main columns).
- **F = 142 main** is the union join/open layout R3 splits into J (~134) + O
  (~88), paying join width on openings today.
- **C = 50 main × 3 rows/leaf** + the D row is the ~223-base-cell/leaf cost R3
  fuses into one ~93-cell L row.

## 3. Golden roots / opcode streams

The authoritative golden corpus is the **cross-language differential corpus**:

- generator: `vectors/gen_vectors.py` (mirrors `rsmt6a.py`);
- data: `crates/rsmt-core/tests/vectors.txt` (~10² rounds, byte-exact roots +
  `S/O/OL/L/N` streams);
- consumer: `crates/rsmt-core/tests/differential.rs` (asserts the Rust core is
  byte-identical to Python).

This pins the retained RSMT semantics. **M1 update (done):** the corpus was
**regenerated with exact 32-byte values** (`gen_vectors.py` now emits
`getrandbits(256).to_bytes(32)`); `differential.rs` parses each value as a
`Value32`. The differential test remains byte-identical to `rsmt6a.py` (10²
rounds), confirming only the leaf-value *encoding* changed while opcode streams,
topology, and node hashing are unchanged. The inline `golden_root_and_stream`
test's opcode stream is unchanged; only `GOLDEN_ROOT` was recomputed from Python
(`39a6093…30b42f`). New M1 tests (`crates/rsmt-core/tests/canonical_types.rs`)
prove short/long values are rejected, leading zeros retained, all-zero handled,
the checked limb constructor rejects over-wide limbs, and `None` old root is
distinct from a present all-zero digest. A byte↔limb↔Poseidon2 leaf differential
lives in `rsmt-hash` tests.

## 4. API status (M0-⑨)

`crates/rsmt-prover/src/round.rs::prove_and_verify_round` is annotated
**EXPERIMENTAL — not an external-verifier security boundary**. It proves and
verifies in one process against prover-built preprocessing, takes a caller `seed`
that derives the Poseidon2 proof-hash constants, and accepts a caller
`ProverConfig`. It is retained only as a differential/performance oracle until the
M7 `prepare_verifier` / `prove_round` / `verify_round` split; it is not the
production protocol.
