# Verification status

Native corollaries are native for CPU rows only. Cached CPU certificates supply
CPU equations and decoder lookup; bigint, extended-round, G and special5 worker
equations remain no-cache flat-constraint premises. Split Keccak uses direct
imported worker constraints and source setup certificates, with no compiler capture.
Compiler preservation covers 11 cached compilations.

All three targets currently cover one initialization/teardown instance, with
several windows allowed within that instance. Rust accepts several such instances
and checks distinct windows across the concatenated list; that aggregation is
not covered. Generalizing the boundary and boot-seed proof to a list remains
pending. `workerFamilies` and absent split pools restrict submitted circuit
instances; they are not derived solely from public program no-call premises.

## Proofs

All three machine targets are proved.
Their definitions stay unchanged. Cached Review claims remain.
Uncached-only Review cases and statements are removed with user approval.
The split Keccak source certificates are proved.
Exact lookup, request and RAM premises stay explicit.
The verified base is `c1a662222cafcd96db4383dce737edb79fa62b09`.
Production functions match the base. Only additive artifact exports and their
required serialization derives remain outside the formal model and CI.
The initialization-window defect is fixed upstream by #548 in this base. The
redundant branch-only repair is removed; see [FINDINGS.md](FINDINGS.md).

## Current checkpoint

The 4 November specification review makes the existing one-instance
initialization and submitted-pool premises explicit. Native corollaries certify
CPU rows only; standard worker equations remain no-cache flat constraints and
split workers have no compiler capture. A new Review statement forwards the
existing 361-call native split permutation theorem without changing its premises.
Current-guide links/anchors, workflow export lists and replay-stack settings pass
static checks. The wrapper and current source tree still require Lean CI validation.


The 4 November production-scope cleanup restores every existing production
function to the base. A static diff audit checks exact restored bytes, unchanged
setup bodies and serialization-only derives. Exporter formatting passes.
Native source receipts have ten mismatches against the retained setup manifest;
[FINDINGS.md](FINDINGS.md) records them pending fresh-export requalification.
No full FV result qualifies this cleanup yet.

Warm run [41803197805](https://github.com/matter-labs/zksync-airbender/actions/runs/41803197805)
failed in source validation on reserved `start` binders in
`Proofs/UnifiedReduced/WorkerExecution.lean`. The binders and their uses are now
escaped without changing their Lean names or theorem statements. This source
repair still needs CI validation; no duplicate local build is running.

The tag `fv-archive-uncached` records the branch before scope removal.

The uncached captures and captured-program compatibility modules are removed.
Old arithmetic, functional and frame shard projections are removed.
All 58 focused source builds for this deletion pass.
The cached native acceptance theorems remain in the production gate.
Three [native corollaries](Airbender/Review/Compiler/Theorems.lean) compose them
with the full unsigned, reduced and unified target proofs.
Their focused source builds pass.
Item 3 has stopped. No more fact families will be converted.
FV CI is configured for weekly full assurance and manual iteration runs on the large runner.
The weekly schedule starts when the workflow reaches the default branch.
One freshness step checks all 52 generator routes.
It also requires tracked Airbender imports to resolve to tracked sources.
The cold source queue includes the top-level `Airbender.lean` module.
Its focused source build passes after the stale imports are removed.
The tracked-import check covers 12,078 imports in 4,212 Lean files.
The earlier log is in [VERIFICATION_HISTORY.md](VERIFICATION_HISTORY.md).
The final axiom inventory and baseline refresh remain pending.
[PR #585](https://github.com/matter-labs/zksync-airbender/pull/585) is open and mergeable.
One full assurance run, including independent kernel replay, remains required before merge.
The history rewrite signed all 768 commits. Later commits are signed.
GitHub verifies the signed head.
The signing rewrite leaves the source tree unchanged.

## Plan

1. The three deletion commits are complete. Their focused source builds pass.
2. Iterate with a warm manual run on the large runner. It retains normal Lake
   freshness, the complete frontend and runtime checks, generator freshness,
   and the environment/axiom audit. The cold benchmark and independent replay
   are not in this iteration gate.
3. After iteration, run full assurance once with transitive kernel replay and
   the false-proof controls. Use a 2,048 MiB stack and refresh the axiom
   baseline. Weekly default-branch runs also include this assurance. Request
   a cold source benchmark separately when new performance data is needed.
4. Fix proof and validation failures within the formal model and CI. Record
   production defects in FINDINGS.md and expose the required property as a
   temporary interface assumption. Do not repair production behavior here.

## Runtime

The user moved final validation to the large CI runner.
[Run 41451555538](https://github.com/matter-labs/zksync-airbender/actions/runs/41451555538)
stopped at signed commit `6031819e9f8e76f4acc351a0b1af8c8bf7ee5dd3`.
All 12 native generators, all 16 setup exports, the complete setup inventory,
and the compiler-capture freshness checks pass. The cold pass built 2,756 modules.
The next module rejected the reserved `parts` binder in `ShiftAssembly.lean`.
The fix quotes that binder and the same reserved syntax in two adjacent consumers.
The Lean names and theorems stay unchanged.
All three focused source builds and all 52 generator checks pass.
CI now saves cold build progress after failure.
[Run 41546838677](https://github.com/matter-labs/zksync-airbender/actions/runs/41546838677)
then stopped after 756 modules when Linux rejected a `pidfd_open` request.
The guard now retries this error briefly and rechecks process identity and exit.
It still stops if it cannot pin a live process. Resource caps stay unchanged.
The focused Linux guard controls pass. A corrected full run is required.
The earlier run rejected three omitted split Keccak exports. The CI list is fixed.
The repaired run reuses saved native build caches.
The registered Rust CI workflow provides the manual entry.
It calls the same FV workflow. Other Rust jobs skip this manual run.
FV stays off PR runs. Nightly runs retain their normal baseline comparison.
This manual run requests a cold build and a baseline refresh.
It restores no project Lean objects. Each cold module gets a time and memory receipt.
The job exports the refreshed baseline only after a passing environment audit.
The transitive replay uses a 2,048 MiB stack and checks all safe dependencies.

The duplicate local Mac frontend and Docker cold run stopped at the user's request.
Their caches and partial reports remain. Neither is a full validation result.
The separate Lean 4.35 experiment has completed its focused source checks.
That experiment does not change this PR's Lean 4.31 toolchain.

Focused builds pass for the cached native acceptance path, all three native
corollaries and the changed compiler/protocol aggregate imports.
All 52 generator routes pass. These focused results do not replace the full gate.
`Source.ChiCharacters` uses the measured 1,800-second source allowance.
Other source leaves retain 900 seconds. Memory caps and kernel checks stay unchanged.

## Final validation

| Phase | State | Time (s) | Peak footprint (MiB) |
| --- | --- | ---: | ---: |
| CI cold source partial, 2,756 of 4,202 modules | Stopped at parse failure | 33,462.48 | 2,198.55 |
| CI `ShiftAssembly` parse failure | Fixed; focused source passes | 4.62 | 353.58 |
| CI cold source partial, 756 of 4,202 modules | Stopped at guard error; fixed | 11,130.39 | 2,278.52 |
| CI full frontend and runtime gates | Queued | Pending | Pending |
| CI environment audit and baseline refresh | Queued | Pending | Pending |
| CI full transitive replay, 2,048 MiB stack | Queued | Pending | Pending |
| Local Linux cold partial, 857 modules | Stopped; moved to CI | 8,383.54 | 2,202.59 |
| Local Mac frontend partial | Stopped; moved to CI | 5,108.33 | 2,100.26 |
| Local Linux `Source.ChiCharacters` cold leaf | Passed | 1,133.67 | 540.31 |

The CI and Linux partial times sum module guard times. The Mac time is wall time.
The failed CI artifact retains `cold-build/modules.jsonl` and all failure logs.
The complete cold pass will also export `cold-build/modules.md`.
These times include Lake startup and dependency freshness checks.
CI uploads commands, resource receipts and failure logs from each stage.
Local partial evidence remains in `/tmp/airbender-review-round/method-reset-2026-11-02/`.
No duplicate local full audit or replay is scheduled.
The PR monitor follows the CI run and reports failed verification steps even
while cache-saving cleanup is still running.

## PR checks

Earlier passing PR checks apply to their recorded revisions, not this cleanup.
The branch-only initialization-window test is removed; upstream #548 already
pins deployment top bits and rejects differing preimage values. The GPU workflow,
including its original RAM setting, is restored to the base.

Production crate additions are limited to the artifact export examples, the setup
artifact module and tests, its module declaration, and required serialization
derives. Cache-mode setup selection lives only inside the export example.
The final PR description lists every file outside `formal_verification/` and
its artifact or CI purpose. Current ordinary checks, native receipt
requalification and the separate full FV gate must pass before merge.
