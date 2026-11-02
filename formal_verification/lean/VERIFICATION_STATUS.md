# Verification status

## Proofs

All three machine targets are proved.
Their definitions and all Review statements stay unchanged.
The split Keccak source certificates are proved.
Exact lookup, request and RAM premises stay explicit.
The verified base is `c1a662222cafcd96db4383dce737edb79fa62b09`.
The local initialization-window fix remains in this branch.

## Current checkpoint

Commit `f5840e274` records the current memory payload work.
The existing source and direct-consumer checks passed for the final 18 captures.
Generator freshness passed. The family rollout has stopped.
The earlier log is in [VERIFICATION_HISTORY.md](VERIFICATION_HISTORY.md).
The axiom inventory has not been refreshed for this checkpoint.

## Plan

1. Remove uncached captures from the gate.
   Delete the captured-program compatibility layer and its unused dependencies.
   Delete old internal shard declarations and projection wrappers.
   Preserve all Review statements and the three machine targets.
2. Use one codec, generator, freshness check and CI step.
3. At the end, run the cold full Linux build and transitive replay.
   Record module time, peak memory and totals in one table.
   Use the lakefile stack for replay: 2,048 MiB.
4. Use the measured costs to select any further conversion.
   Stop item 3 when the build and replay fit the CI windows.
5. For each commit, run focused builds and generator freshness only.
   Run the full frontend, environment audit and axiom refresh at the end.

## Runtime

This host runs macOS. The user enabled Docker.
Linux checks and baseline measurements are deferred to the end.
They have not started. No Linux result is claimed.
Existing caches and preservation objects remain in `/tmp/airbender-review-round/`.

The known aggregate import collision remains unresolved.
It names `Airbender.WordMemory.importedConstraintsTraceColumns.eq_1`.
The same collision occurs with the earlier arithmetic objects.
No aggregate frontend pass is claimed.

## Final validation

The final cold build, full frontend, full transitive replay, environment audit
and axiom baseline refresh remain pending.
The hourly task follows this plan. It must not restart the family rollout.
