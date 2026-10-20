# Complete Keccak permutation

This directory states the complete permutation effect of a 649-call Keccak span,
binding Clean's original reference to actual initial/final lane reads. Call and
window contracts retain seed timestamps and protocol scope, while shared execution
connects the final state to native terminal tokens.

## Checked results

[`Native.operation_execution`](../../../../../slop/Slop/Final/Trace/Workers/Keccak/Theorems.lean) proves actual port/lane effects
for all seven native modes under the modeled controller.
[`Native.permutation_soundness` and `Native.permutation_boundary_soundness`](../../../../../slop/Slop/Final/Trace/Workers/Keccak/Theorems.lean)
prove the original full permutation on actual boundary lanes, with shared terminal
agreement. [`Native.window_soundness`](../../../../../slop/Slop/Final/Trace/Workers/Keccak/Theorems.lean) binds the first complete span
at retained cut states; later workers may remain outside the window.
Public protocol/domain/alignment/table conditions remain inputs.

Read [Theorems](../../../../../slop/Slop/Final/Trace/Workers/Keccak/Theorems.lean), [Call](Call.lean) and
[BoundaryCall](BoundaryCall.lean). [Permutation](Permutation.lean) binds
the original complete reference to actual initial/final lane reads.

[Windows](Windows.lean) selects the first complete 649-call span.
Initialized matching derives the control schedule, fixed pointer, lane/scratch
coverage and linked intermediate states. Keep native seed timestamps, modeled
controller tables, public domain and complete-span ABI visible.

[Local modes](../../../Circuits/Keccak/README.md) have a narrower scope.
Invalid-control fallback does not establish the 24-round protocol.
[Caller composition](../../Delegation/README.md) and
[prepared unified spans](../../UnifiedReduced/README.md) retain separate prefix
and preparation restrictions; completion does not imply automatic restart.
