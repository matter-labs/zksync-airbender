# Verification status

The model covers only the cached circuits. Production sets use_caches = true.

## Proofs

All three machine targets are proved.
Their definitions stay unchanged. Cached Review claims remain.
Uncached-only Review cases and statements are removed with user approval.
The split Keccak source certificates are proved.
Exact lookup, request and RAM premises stay explicit.
The verified base is `c1a662222cafcd96db4383dce737edb79fa62b09`.
The local initialization-window fix remains in this branch.

## Current checkpoint

The tag `fv-archive-uncached` records the branch before scope removal.

The uncached captures and captured-program compatibility modules are removed.
Old arithmetic, functional and frame shard projections are removed.
All 58 focused source builds for this deletion pass.
The cached native acceptance theorems remain in the production gate.
Three [native corollaries](Airbender/Review/Compiler/Theorems.lean) compose them
with the full unsigned, reduced and unified target proofs.
Their focused source builds pass.
Item 3 has stopped. No more fact families will be converted.
FV CI runs nightly and on manual dispatch, on the large runner.
One freshness step checks all 52 generator routes.
The earlier log is in [VERIFICATION_HISTORY.md](VERIFICATION_HISTORY.md).
The final axiom inventory and baseline refresh remain pending.

## Plan

1. The three deletion commits are complete. Their focused source builds pass.
2. Run FV only at night or on manual dispatch, on the large runner.
   Use one generator freshness step. Keep the existing checkers.
3. Run one final cold build, full frontend and transitive kernel replay.
   Use a 2,048 MiB stack. Run the environment audit and refresh the baseline.
   Record module time, peak memory and totals in one table.
4. Fix only validation failures. Do not change a target or cached Review claim.

## Runtime

This host runs macOS. The user enabled Docker.
The final Linux run has started in an isolated Docker volume.
It uses the pinned ARM64 Lean toolchain and no Mac build objects.
Bootstrap passed. The cold build covers all 4,201 retained source modules.
No full Linux validation result is claimed.
A timing-helper conflict stopped the first bootstrap attempt.
The retry uses the unchanged compiler and normal guarded module builds.
Existing caches and preservation objects remain in `/tmp/airbender-review-round/`.

Focused source builds pass for the cached native acceptance path, all three
native corollaries and the changed compiler/protocol aggregate imports.
The single generator freshness command passes for all retained routes.
The aggregate source builds use retained objects. They are not a clean full
frontend result. The earlier ownership collision remains in the history.

## Final validation

| Phase | State | Time (s) | Peak memory (MiB) |
| --- | --- | ---: | ---: |
| Cold Linux source build, 4,201 modules | Running | Pending | Pending |
| Full frontend and runtime gates | Queued | Pending | Pending |
| Environment audit and baseline refresh | Queued | Pending | Pending |
| Full transitive replay, 2,048 MiB stack | Queued | Pending | Pending |

The run uses Docker container `airbender-fv-final-20261102`.
Evidence is in `/tmp/airbender-review-round/method-reset-2026-11-02/linux-final/`.
Normal guarded Lake builds record each module time and peak memory.
These times include Lake startup and dependency freshness checks.
The hourly task follows this plan. It must not restart the family rollout.
