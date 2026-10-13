# Complete G work-vector spans

This directory states the complete 56/80-call G work-vector fold on actual
initial/final RAM, using Clean's original G reference. Call and window contracts
give the public protocol mode/count and native-boundary conditions. Shared history
connects all calls and terminal tokens without supplied intermediate states.

Read [Theorems](Theorems.lean), then [Call](Call.lean) and
[BoundaryCall](BoundaryCall.lean) for public initialization versus retained
native-boundary timestamps. [WorkVector](WorkVector.lean) is the complete
56/80-call fold using the original Clean G.

[Windows](Windows.lean) selects spans after whole preceding spans.
Check public mode/count, tracked alignment and modeled tables.
Accepted initialized history derives the schedule, controls, pointers,
intermediate states and actual initial/final RAM reads.

[Local circuit review](../../../Circuits/Blake2G/README.md) covers one G operation.
[Caller composition](../../Delegation/README.md) and
[unified windows](../../UnifiedReduced/README.md) retain distinct shared-prefix
and preparation/chaining scopes. Zero-clock surplus effects remain visible.
