# M10: FRI parameter grid and the chosen production configuration

`DEVPLAN-R3.md` M10 / §6.4. The S-box register count (0/1) and Poseidon2 vector
length (4/8/16) are **compile-time** constants of Table B, so a runtime grid
cannot sweep them (they need separate builds; deferred). The FRI parameters are
runtime-configurable, so this grid measures them directly, targeting §6.4's
preference for a **no-grinding** candidate over `100 queries + 16 PoW bits`.

## Measured grid (prefill 1024, batch 64, release, single run)

`r3round::tests::m10_fri_grid`. Conjectured bits = `log_blowup·queries + PoW`.

| log_blowup | queries | PoW | bits | prove ms | verify ms | proof KB |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 100 | 16 | 116 | 128 | 87 | 1997 |
| 1 | 116 | 0 | 116 | 119 | 99 | 2303 |
| 2 | 58 | 0 | 116 | 179 | 65 | 1218 |
| **2** | **64** | **0** | **128** | 180 | 67 | 1335 |

## The four axes — proving time is not the only goal

A production choice must balance **security bits, proof size, proving time, and
recursion friendliness**, ideally with simple parameters. Reading the grid:

- **Grinding is pure loss.** `(1,100,16)` spends ~15 ms on a 16-bit PoW grind;
  dropping it (`1,116,0`) reaches the same 116 bits and proves faster. Grinding
  is also a serial hash loop that is very expensive to re-verify **inside a
  recursive verifier**, so it earns nothing on any axis.
- **Rate ¼ (`log_blowup=2`) is the recursion win.** It halves the query count
  (58–64 vs 116) for the same bits. Each FRI query is a Merkle-path opening the
  recursive verifier must check in-circuit, so **fewer queries → a materially
  smaller recursive verifier**. Rate ¼ also gives the **smallest proof**
  (~1.2–1.3 MB, −33 %) and the **fastest verify** (~65 ms). Its cost is prover
  time (+~40 %, the doubled LDE) — a one-time prover expense, not paid by the
  many downstream/recursive verifiers.

## Decision

Adopt **`(log_blowup = 2, num_queries = 64, query_pow_bits = 0)`** as the
production `R3_FRI`:

- **128 conjectured bits** — a clean power-of-two query count with comfortable
  margin over the 116-bit target (`04-soundness-budget.md`);
- **no grinding** — nothing to re-run in a recursive verifier;
- **64 query openings** — half the in-circuit Merkle work of a rate-½ config;
- **~1.3 MB proof, ~67 ms verify** — smallest/fastest tier;
- **simple**: rate ¼, 64 queries, no PoW.

The prover pays ~40 % more time (the rate-¼ LDE); this is the deliberate trade —
proving is one-time, whereas proof size, verify time, query count, and
grinding-freedom all directly help every downstream and recursive verifier.

`(1,116,0)` remains the documented alternative when **prover throughput** is the
priority (fastest prove, but 2.3 MB proof and 116 queries). Switching is a
one-line `R3_FRI` change plus a tag bump.

Per the plan, changing the FRI parameters is a protocol change: `R3_FRI` is
`rsmt-protocol`-owned and the `ProtocolId` tag is bumped to `R3P2v003`. The
S-box-register / vector-length sweep (compile-time `table_b` constants) and
warmed-median measurements on a pinned machine remain future work; they do not
change soundness — Table B dominates and the arithmetization is baseline-speed.
