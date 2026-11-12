# Complete G work-vector spans

This directory states the complete 56/80-call G work-vector fold on actual
initial/final RAM of the `RV.State`, using Clean's original G reference. Call and window contracts
give the public protocol mode/count and native-boundary conditions. Shared history
connects all calls and terminal tokens without supplied intermediate states.

## Checked results

[`Native.rv_operation_execution`](../../../../../proven/Proven/Final/Trace/Workers/Blake2G/RVTheorems.lean) connects each G row to actual
port effects. [`Native.rv_workvector_soundness`](../../../../../proven/Proven/Final/Trace/Workers/Blake2G/RVTheorems.lean) additionally proves
the complete reference fold on actual initial/final RAM and terminal tokens.
[`Native.rv_workvector_boundary_soundness` and `Native.rv_window_soundness`](../../../../../proven/Proven/Final/Trace/Workers/Blake2G/RVTheorems.lean)
retain native seeds and derive boundary controls/intermediate states under the
public mode/count, alignment/domain, modeled-table and matching conditions.

Read [RVTheorems](RVTheorems.lean), then
[RVCall](RVCall.lean): `RVCallInputs` (public initialization), `RVNativeCallInputs` (retained
native-boundary timestamps) and `RVWindowInputs` (a span after whole preceding spans). [WorkVector](WorkVector.lean) is the complete
56/80-call fold using the original Clean G.

Check public mode/count, tracked alignment and modeled tables.
Accepted initialized history derives the schedule, controls, pointers,
intermediate states and actual initial/final RAM reads.

[Local circuit review](../../../Circuits/Blake2G/README.md) covers one G operation.
[Caller composition](../../Delegation/README.md) and
[unified windows](../../UnifiedReduced/README.md) retain distinct shared-prefix
and preparation/chaining scopes. Zero-clock surplus effects remain visible.
