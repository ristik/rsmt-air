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
| 1 | 100 | 16 | 116 | 131.7 | 88.0 | 1997 |
| **1** | **116** | **0** | **116** | **116.8** | 98.9 | 2303 |
| 1 | 132 | 0 | 132 | 118.6 | 114.0 | 2609 |
| 2 | 58 | 0 | 116 | 176.4 | 61.8 | 1218 |

## Reading

- **Grinding is a net loss here.** The current `(1,100,16)` spends ~15 ms grinding
  16 PoW bits; the no-grinding `(1,116,0)` reaches the same 116 conjectured bits
  and proves **faster** (116.8 vs 131.7 ms). Grinding is also awkward inside a
  recursive verifier (§6.4), so it earns nothing.
- **Higher blowup trades prove time for proof size + verify time.** `(2,58,0)`
  gives the smallest proof (1218 KB, −39 %) and fastest verify (61.8 ms) but the
  slowest prove (176 ms, +34 %) because the LDE doubles.

## Decision

Adopt **`(log_blowup=1, num_queries=116, query_pow_bits=0)`** as the production
`R3_FRI`:

- **fastest prove** of any candidate, and faster than the pre-M10 baseline;
- **no grinding** — the §6.4 preference, and recursion-friendly;
- meets the 116-bit standalone target (`04-soundness-budget.md`).

`(2,58,0)` remains the documented alternative if a deployment prioritizes proof
size / verify time / recursion depth over prover throughput; switching to it is a
one-line `R3_FRI` change plus a protocol-tag bump.

Per the plan, changing the FRI parameters is a protocol change: `R3_FRI` is
updated in `rsmt-protocol` and the `ProtocolId` tag is bumped `R3P2v001 →
R3P2v002`. The S-box/vector-length sweep and warmed-median measurements on a
pinned machine remain future work (they do not change soundness — Table B
dominates and the arithmetization is already baseline-speed).
