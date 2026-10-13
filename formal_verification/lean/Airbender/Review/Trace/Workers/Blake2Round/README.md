# Complete extended-BLAKE compression

This directory states complete seven-/ten-round extended-BLAKE compression on
actual boundary blocks. Protocol inputs specify flags and span scope; modeled
controllers and initialized history connect preparation, mixing and chaining
through the actual Sail states. Selected windows retain their native timestamps
and controller-prefix restrictions.

Read [Theorems](Theorems.lean), [Call](Call.lean) and
[BoundaryCall](BoundaryCall.lean). [Compression](Compression.lean) names
the complete seven-/ten-round reference and actual initial/final block reads.

[Windows](Windows.lean) selects a first span within one ten-position controller.
Check public flags/count, retained seed timestamps, tracked alignment and modeled tables.
History derives exclusive masks, fixed pointers, readonly messages, intermediate
states and terminal agreement. Later rounds may remain outside a selected window.

[Local phases](../../../Circuits/Blake2Round/README.md) do not alone establish compression.
Completion controls do not automatically restart the protocol.
[Prepared unified spans](../../UnifiedReduced/README.md) retain their public
preparation, duration and empty worker-prefix restrictions.
