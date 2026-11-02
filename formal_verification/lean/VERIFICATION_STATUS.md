# Upgrade experiment status

The model covers only the cached circuits. Production sets use_caches = true.

## Branch and scope

This is `codex/lean-turbo-upgrade`.
It forks from signed commit `100c270a0ec1837701e7b0bf2b7385e5cdee2cab`.
Lean and Mathlib resolve at version 4.35.0.
Clean and lean-sail keep their exact reference revisions.
All three target definitions and cached Review statements stay unchanged.
The complete proof port remains unqualified on Lean 4.35.
Earlier whole-project evidence describes Lean 4.31.

[PR #585](https://github.com/matter-labs/zksync-airbender/pull/585) stays separate.
Its [full FV run](https://github.com/matter-labs/zksync-airbender/actions/runs/41451555538)
uses Lean 4.31 on the large runner.
The user moved full validation there and freed the Mac for this experiment.
No second full validation is required for the initial experiment.
Full official validation is required before adopting the upgrade.

## Completed focused checks

Dependency resolution and the existing Clean compatibility patches pass.
All 52 source generator checks pass.
The real `FiniteGridChecks` source compiles with stock Lean 4.35.
The numeric query-frame checker and strict importer compile with stock Lean 4.35.
Their dependency builds include the pinned Clean field, vector, channel, equality
and offline-memory proofs. Hash checks protect all reference patches.
Proof reductions and theorem-name updates leave statements unchanged.
The pinned turbo tool passes `cargo check` and its release build.
An exact core-only source copy passes stock Lean and the standard turbo kernel.
The repeat turbo check returns a checked theorem cache hit.
The smoke launcher verifies exact source and policy hashes after each command.
No production circuit, Rust code, proof statement or matching premise changes.

## Current limits

The pinned turbo tool rejects the real Lake library's `needs` dependencies.
They protect artifact freshness and remain in place.
The isolated smoke does not qualify whole-project integration or speed.
No warm proof-edit measurement is claimed.
A focused security review and RustSec graph scan are complete.
The scan reports no known dependency advisories. This is not a security certificate.
The launcher now clears inherited compiler-simplification exceptions too.
Further turbo execution requires a disposable OS sandbox without host credentials.
The time and memory guard does not provide OS isolation.
The remaining proof port still needs focused dependency and consumer builds.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
The official kernel remains the acceptance gate.

## Measurements

| Focused phase | Time (s) | Peak footprint (MiB) |
| --- | ---: | ---: |
| Serial tool check and release build | 264.39 | 1,030.80 |
| Smoke group, stock plus two turbo commands | 4.71 | 149.40 |
| Stock source command | 1.47 | Within smoke group |
| Turbo first theorem check, setup warm | 1.83 | Within smoke group |
| Turbo repeat cache hit | 0.79 | Within smoke group |

[TURBO_LEAN.md](TURBO_LEAN.md) gives the exact scope and reproduction command.
Evidence remains in `/tmp/airbender-turbo-2026-11-02/`.
The initial tool setup and the later warm setup are distinct.
No full frontend, audit, baseline refresh or transitive replay is claimed here.
