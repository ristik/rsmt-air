# M11 dependency / release audit (`cargo audit`)

Run at the M11 cut-over. `cargo audit` scans `Cargo.lock` (177 crate deps)
against RustSec.

## Fixed

- **RUSTSEC-2026-0204** — `crossbeam-epoch 0.9.18` (invalid pointer dereference in
  the `fmt::Pointer` impl for `Atomic`/`Shared`). This is the Rayon/crossbeam
  advisory path flagged in `DEVPLAN-R3.md` §4/M11. **Resolved** by
  `cargo update -p crossbeam-epoch` → `0.9.20` (`>= 0.9.20` is the fixed range).
  It is a transitive dependency via `rayon`; the bump is a patch update and the
  workspace builds and passes all tests unchanged.

After the update: **0 vulnerabilities**.

## Accepted residual warnings (unmaintained / unsound / yanked)

These are informational RustSec *warnings*, not vulnerabilities, and are all
transitive or low-exploitability in this workspace. Accepted with rationale;
revisit on the next Plonky3 pin bump.

| Advisory | Crate | Kind | Rationale |
|---|---|---|---|
| RUSTSEC-2025-0141 | `bincode 2.0.1` | unmaintained | Used only for internal proof/test serialization at the protocol boundary; the R3 canonical decoder (`rsmt-protocol`) is what gates untrusted bytes, not bincode. No known CVE. |
| RUSTSEC-2024-0436 | `paste 1.0.15` | unmaintained | Compile-time macro pulled in transitively (Plonky3); no runtime surface. |
| RUSTSEC-2026-0190 | `anyhow 1.0.102` | unsound | Unsoundness is in `Error::downcast_mut()`, which this workspace does not call; transitive. |
| — | `spin 0.10.0` | yanked | Transitive (lock-free primitives); a yank is not a vulnerability. Picked up on the next `cargo update`. |

## Policy

`cargo audit` should run in CI (`DEVPLAN-R3.md` §4). The residual warnings above
are the documented accepted exceptions; any **new** advisory of severity
"vulnerability" fails the gate and must be fixed or explicitly re-accepted here
with exploitability and expiry.
