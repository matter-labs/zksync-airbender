# Complete extended-BLAKE compression

This directory states complete seven-/ten-round extended-BLAKE compression on
actual boundary blocks. Protocol inputs specify flags and span scope; modeled
controllers and initialized history connect preparation, mixing and chaining
through the actual Sail states. Selected windows retain their native timestamps
and controller-prefix restrictions.

## Checked results

[`rv_operation_execution`](../../../../../slop/Slop/Final/Trace/Workers/Blake2Round/RVTheorems.lean) proves local phase effects with the
standalone exclusive-mask ABI still explicit. [`rv_compression_soundness`](../../../../../slop/Slop/Final/Trace/Workers/Blake2Round/RVTheorems.lean)
and [`rv_compression_boundary_soundness`](../../../../../slop/Slop/Final/Trace/Workers/Blake2Round/RVTheorems.lean) prove the complete reference
output on actual RAM, linked to every terminal token; [`rv_window_soundness`](../../../../../slop/Slop/Final/Trace/Workers/Blake2Round/RVTheorems.lean)
does so at selected first-span cut states within the ten-position controller.
Reads, ranges and intermediate states are derived. Unrestricted restart/chaining and
full mixed caller retirement remain separate.

Read [Theorems](../../../../../slop/Slop/Final/Trace/Workers/Blake2Round/RVTheorems.lean), [Call](Call.lean) and
BoundaryCall. [Compression](Compression.lean) names
the complete seven-/ten-round reference and actual initial/final block reads.

Windows selects a first span within one ten-position controller.
Check public flags/count, retained seed timestamps, tracked alignment and modeled tables.
History derives exclusive masks, fixed pointers, readonly messages, intermediate
states and terminal agreement. Later rounds may remain outside a selected window.

[Local phases](../../../Circuits/Blake2Round/README.md) do not alone establish compression.
Completion controls do not automatically restart the protocol.
[First prepared unified spans](../../UnifiedReduced/PreparedRoundWindows.lean)
retain their public preparation, duration and empty worker-prefix restrictions.
The broader [`Caller.rv_prepared_protocol_sequence_soundness`](../../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean)
supports explicit LUI restarts between compression spans in one continuous mixed
history. Raw matching derives masks within each controller region; earlier workers
remain in the prefix. Every extended-round worker must belong to one such region,
and each region retains its local ten-position cap. Complete span counts, durations,
mode/flags and literal preparation remain explicit; completion alone never restarts.
