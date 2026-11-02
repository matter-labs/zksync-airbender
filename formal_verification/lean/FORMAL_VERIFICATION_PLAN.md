# Verification plan

## Current claims

All three production machine targets are proved.
The split Keccak source certificates are proved.
The cached native acceptance theorems remain in the gate.
One Review corollary for each machine composes native acceptance with its target.
Exact lookup, request and RAM matching remain explicit.

The model covers only the cached circuits. Production sets use_caches = true.
The tag `fv-archive-uncached` retains the earlier scope in git history.
The tree contains no unchecked archive of removed Lean proofs.

## Implementation order

1. Delete uncached captures and captured-program compatibility modules.
   Delete dependencies used only by those modules.
   Keep the three target definitions and the cached production claims.
2. Delete old internal shards and compatibility projections.
   Use existing whole-check soundness facts directly.
3. Run FV at night and on manual dispatch, on the large runner.
   Use one generator freshness step. Keep the existing checkers.
4. Run the local frontend, environment audit and full transitive kernel replay.
   Refresh the axiom baseline. Use the preserved Mac caches.
   Keep the cold Linux build in the background. Finish Linux qualification last.
   Record per-module time, peak memory and totals in one table.
5. Fix only failures. Item 3 has stopped. Do not convert more fact families.

Each deletion commit runs focused source builds of its importers only.
A background cold build must not block other work.

## Proof contract

Use kernel proofs only.
The permitted axioms are propext, Classical.choice and Quot.sound.
Do not use native_decide, new axioms or skipped kernel checks.
Keep the original reference functions and production circuits.
Record circuit discrepancies and use narrow explicit proof assumptions.
Do not change production Rust to make a proof pass.

Real workers retain the shared aggregate owner.
The footprint cap is 2,560 MiB. The resident cap is 5,120 MiB.
The ordinary worker deadline is 900 seconds.
Replay uses the lakefile thread stack: 2,048 MiB.
The guard records both the Lean thread and process stack limits.

## Evidence

[Verification status](VERIFICATION_STATUS.md) gives the current state.
[Verification history](VERIFICATION_HISTORY.md) retains the earlier dated log.
No old partial check establishes the final assurance result.
