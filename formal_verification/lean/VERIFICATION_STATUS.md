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
The earlier log is in [VERIFICATION_HISTORY.md](VERIFICATION_HISTORY.md).
The final axiom inventory and baseline refresh remain pending.

## Plan

1. Finish the three deletion commits. Run focused source builds of importers.
2. Run FV only at night or on manual dispatch, on the large runner.
   Use one generator freshness step. Keep the existing checkers.
3. Run one final cold build, full frontend and transitive kernel replay.
   Use a 2,048 MiB stack. Run the environment audit and refresh the baseline.
   Record module time, peak memory and totals in one table.
4. Fix only validation failures. Do not change a target or cached Review claim.

## Runtime

This host runs macOS. The user enabled Docker.
Linux checks and baseline measurements are deferred to the end.
They have not started. No Linux result is claimed.
Existing caches and preservation objects remain in `/tmp/airbender-review-round/`.

Focused source builds pass for the cached native acceptance path, all three
native corollaries and the changed compiler/protocol aggregate imports.
The single generator freshness command passes for all retained routes.
The aggregate source builds use retained objects. They are not a clean full
frontend result. The earlier ownership collision remains in the history.

## Final validation

The final cold build, full frontend, full transitive replay, environment audit
and axiom baseline refresh remain pending.
The hourly task follows this plan. It must not restart the family rollout.
