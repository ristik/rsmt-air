# R3 measured cost vs the pre-R3 baseline

Validates the `DEVPLAN-R3.md` §5.1 layout projections with real measurements from
`r3round::r3_round_cells` + a timed `prove_and_verify_r3_round`, against the M0
baseline (`05-baseline.md`). Same scenario: **prefill 1024, batch 64**. (The seed
differs, so tree shape differs slightly — 113 vs 114 leaves — but the structural
comparison holds.) `cells = padded_height × (main + prep)`.

## Per-table cells

| Table | R3 real | R3 padded | R3 main | R3 cells | | Baseline | base cells |
|---|---:|---:|---:|---:|---|---|---:|
| A | 565 | 1024 | **33** | 36 864 | | A (37) | 40 960 |
| B | 143 | 256 | 2384 | 614 400 | | B (2384) | 614 400 |
| **L** | 113 | 128 | **93** | **12 032** | | **C+D** | **33 856** |
| **J** | 282 | 512 | 142 | 73 216 | | **F** (join+open) | 74 240 |
| **O** | 9 | 16 | **89** | **1 440** | | — | — |
| R | 2047 | 2048 | 1 | 8 192 | | R | 8 192 |
| P | 31 | 32 | 1 | 128 | | P | 128 |
| **total** | | | | **746 272** | | | **771 776** |

## What the numbers confirm

- **Leaf fusion (C+D → L) is the big win:** leaf cells drop from **33 856**
  (Table C's three 50-wide sponge rows per leaf + Table D's 72-prep batch row) to
  **12 032** (one 93-wide L row per leaf) — a **~64 % reduction** on leaf work,
  matching §5.1's "one L row ≈ 93 base cells vs ≈ 223 for C+D per leaf." And this
  is the *sounder* layout: L range-checks every key/value digit (S4), which the
  old Table D did not guarantee.
- **J/O split:** openings now cost 89-wide O rows instead of 142-wide union rows;
  with only 9 openings here the absolute saving is small, but it grows with
  opening-rich rounds (and O is where the S5 canonical-region fix lives).
- **Reduced A:** 37 → **33** main columns (dropped `batch_idx`/`opened_idx`/
  `has_advice`/`node_hash_old_needed`).
- **Table B is unchanged** (614 400 cells) — the vectorized Poseidon2 trace is the
  inherent hash cost R3 does not (and soundly cannot) remove. It dominates total
  cells, so the **total drops only ~3.3 %** (746 272 vs 771 776) even though the
  non-B tables fall **~17 %** (123 552 vs 149 056).

## Timing

Release-mode `prove + verify` for this round: **214.5 ms** — indistinguishable
from the baseline's `prove 138 ms + verify 76 ms ≈ 214 ms`. Same speed, because
the B-dominated proving work is identical. R3 buys **soundness** (canonical
regions, occurrence-correct arena, byte-faithful leaves, verifier-independent A)
and a small cell reduction at **no proving-time cost**.

> Timing is single-run, not warmed medians. The full warmed corpus, the B-width /
> S-box / FRI parameter grid, and the LogUp-pairing effect are the M9/M10 work;
> this doc only establishes that the R3 arithmetization is **cost-neutral-or-better
> vs the baseline while being sound**.
