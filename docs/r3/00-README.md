# R3 frozen artifacts (M0)

This directory is the **normative** output of milestone M0 of `DEVPLAN-R3.md`.
It freezes the theorem, the protocol scope, the security model, and the
soundness budget *before* any table is rewritten, so that every later milestone
(M1–M11) can be checked against a fixed target instead of a moving one.

Nothing here depends on the `A/B/L/J/O/R/P` table names or on the current
`A/B/C/D/R/F/P` implementation; the documents are written against the abstract
RSMT relation so they survive the arithmetization change.

| Doc | Content | Plan deliverable |
|---|---|---|
| [`01-security-model.md`](01-security-model.md) | Adversary, required property, assumptions, non-goals, canonical-encoding rules, influence classification, stateful interpretation. | M0-①, M0-③ |
| [`02-relation-and-extraction.md`](02-relation-and-extraction.md) | The exact abstract relation `R_R3(public, witness)` and the extraction vocabulary, independent of table names. | M0-② |
| [`03-rsmt-append-only.md`](03-rsmt-append-only.md) | The RSMT-level theorem (coherent additions ⇒ append-only tree semantics) and the **new-leaf ordering lemma** that lets R3 drop the batch table. | M0-④ |
| [`04-soundness-budget.md`](04-soundness-budget.md) | The R3-D13 combined STARK/FRI + LogUp + Fiat–Shamir calculation, the derived **maximum shape**, and the **per-bus no-wrap** formulas. | M0-⑤, M0-⑥ |
| [`05-baseline.md`](05-baseline.md) | Captured pre-R3 benchmarks, golden roots/streams, and the note marking the combined `prove_and_verify_round` API experimental. | M0-⑦, M0-⑧, M0-⑨ |
| [`06-influence-manifest.md`](06-influence-manifest.md) | Per-column influence classification for `A/B/L/J/O/R/P` and the S1–S12 → code + test map (the M8 audit artifact). | M8 |
| [`07-r3-cost.md`](07-r3-cost.md) | Measured R3 per-table cell cost vs the pre-R3 baseline (validates the §5.1 layout projections). | M8/M11 |

**Status of the underlying implementation.** The starting point is the completed
seven-table build `A/B/C/D/R/F/P` (commit `rsmt6a 1st cut (insecure)`), which
proves and verifies end-to-end (69 tests green). The findings that R3 repairs are
listed in `DEVPLAN-R3.md` §4; this directory does not restate them, it fixes the
target they are repaired *against*.

**What "frozen" means.** Changing any statement in `01`–`04` is a protocol change
and must bump the protocol identifier (see `DEVPLAN-R3.md` §6.1). `05` is a moving
record and is expected to be updated as milestones land.
