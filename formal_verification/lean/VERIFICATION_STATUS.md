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
It also requires tracked Airbender imports to resolve to tracked sources.
The cold source queue includes the top-level `Airbender.lean` module.
Its focused source build passes after the stale imports are removed.
The tracked-import check covers 12,078 imports in 4,212 Lean files.
The earlier log is in [VERIFICATION_HISTORY.md](VERIFICATION_HISTORY.md).
The final axiom inventory and baseline refresh remain pending.
[PR #585](https://github.com/matter-labs/zksync-airbender/pull/585) is in draft.
The history rewrite signed all 768 commits. Later commits are signed.
GitHub verifies the signed head.
The signing rewrite leaves the source tree unchanged.

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
The local final validation uses the preserved Mac caches.
Its import inventory passes after the path-case correction.
The cold Linux build continues in an isolated Docker volume.
It uses the pinned ARM64 Lean toolchain and no Mac build objects.
Bootstrap passed. The current cold queue covers all 4,202 source modules.
The first pass completed 177 modules. `Source.ChiCharacters` then reached
the 900-second limit. The resume retains all completed results and reports
source-character progress. No proof error or memory-limit failure was reported.
`Source.ChiCharacters` passes on Linux in 1,133.67 seconds at 540.31 MiB.
This leaf uses the existing 1,800-second review allowance.
The Mac frontend hit the same 900-second limit and resumes with this allowance.
All other source leaves retain 900 seconds. Memory caps stay unchanged.
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
| Cold Linux source build, 4,202 modules | Resume running after a timeout | Pending | Pending |
| Mac full frontend and runtime gates | Resume after source time-limit fix | Pending | Pending |
| Linux `Source.ChiCharacters` cold leaf | Passed | 1,133.67 | 540.31 |
| Mac environment audit and baseline refresh | Queued | Pending | Pending |
| Mac full transitive replay, 2,048 MiB stack | Queued | Pending | Pending |
| Linux runtime qualification | Deferred until last | Pending | Pending |

The Linux run uses Docker container `airbender-fv-final-20261102`.
It retains the completed module receipts. No second full replay is scheduled.
Local reports are in the sibling `mac-final/` evidence directory.
Evidence is in `/tmp/airbender-review-round/method-reset-2026-11-02/linux-final/`.
Normal guarded Lake builds record each module time and peak memory.
These times include Lake startup and dependency freshness checks.
The hourly task follows this plan. It must not restart the family rollout.

## PR checks

The Rust warnings jobs found a stale call in the initialization-window test.
The test now uses the current five-argument verifier generator.
The generator derives packing and batching parameters from its configuration.
The three warnings jobs, formatting, spelling and EVM verifier jobs pass.
Other PR jobs remain pending. Production code stays unchanged.
