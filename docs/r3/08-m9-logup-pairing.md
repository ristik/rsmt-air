# M9 result: two-entry LogUp pairing is not viable in the pinned Plonky3

`DEVPLAN-R3.md` M9 / §5.9 proposed combining two linear lookup entries into one
running-sum column (e.g. L's 52 digit checks → 26 contexts) to save extension
columns. The plan **mandated a minimal full-FRI regression before touching any
round AIR**, because the historical failure mode was `OodEvaluationMismatch`.

## The gate test and its result

`crates/rsmt-prover/src/logup_pairing.rs` builds a minimal two-AIR batch — a
`Sender` that sends `(value)` on a global bus, and a `Pair` receiver that takes
two values per row — and proves+verifies it through the exact
`prove_batch`/`verify_batch` stack the round uses, in two modes:

- **unpaired** (two separate one-entry contexts): **verifies**;
- **paired** (both receives grouped in one `register_lookup`, one aux column):
  **fails with `OodEvaluationMismatch`**.

Plonky3's own passing two-entry example (`lookup/src/tests.rs::
test_range_check_end_to_end_valid`) uses `Kind::Local` with a **Receive + Send**
pair (which nets to zero within one AIR). Grouping two **same-direction**
receives on a **global** bus — which is what pairing L's digit checks would
require — is not supported by the pinned rev `4b341cc`.

## Decision

Per the risk register ("Two-entry LogUp causes degree/OOD failures → keep one
entry per context for that family; correctness precedes aux savings"), **R3 does
not pair global-bus receives.** Every bus keeps one entry per LogUp context, as
in the working M7 arithmetization.

The gate is retained as a **regression guard**
(`global_two_entry_pairing_is_unsupported_in_pinned_plonky3`): it asserts the
unpaired path verifies and the paired path fails. If a future Plonky3 upgrade
makes global two-entry contexts sound, the second assertion flips and M9 pairing
can be revisited — at which point the extension-column savings in §5.9 (L
52→26, O 26→13, adjacent B/J/O range receives) become available.

## What this cost

Nothing that matters. The pairing was a *column-count* optimization; the
measured total prove time (`07-r3-cost.md`) is dominated by Table B, and the
non-paired arithmetization already matches the baseline's speed while being
sound. The disciplined gate prevented shipping a broken optimization that would
have surfaced as a confusing OOD failure inside the full round.
