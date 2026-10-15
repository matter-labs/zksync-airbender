# Complete extended-BLAKE compression

This directory states complete seven-/ten-round extended-BLAKE compression on
actual boundary blocks. Protocol inputs specify flags and span scope; modeled
controllers and initialized history connect preparation, mixing and chaining
through the actual Sail states. Selected windows retain their native timestamps
and controller-prefix restrictions.

## Checked results

[`operation_execution`](Theorems.lean) proves local phase effects with the
standalone exclusive-mask ABI still explicit. [`compression_soundness`](Theorems.lean)
and [`compression_boundary_soundness`](Theorems.lean) prove the complete reference
output on actual RAM, linked to every terminal token; [`window_soundness`](Theorems.lean)
does so at selected first-span cut states within the ten-position controller.
Reads, ranges and intermediate states are derived. Unrestricted restart/chaining and
full mixed caller retirement remain separate.

Read [Theorems](Theorems.lean), [Call](Call.lean) and
[BoundaryCall](BoundaryCall.lean). [Compression](Compression.lean) names
the complete seven-/ten-round reference and actual initial/final block reads.

[Windows](Windows.lean) selects a first span within one ten-position controller.
Check public flags/count, retained seed timestamps, tracked alignment and modeled tables.
History derives exclusive masks, fixed pointers, readonly messages, intermediate
states and terminal agreement. Later rounds may remain outside a selected window.

[Local phases](../../../Circuits/Blake2Round/README.md) do not alone establish compression.
Completion controls do not automatically restart the protocol.
[First prepared unified spans](../../UnifiedReduced/PreparedRoundWindows.lean)
retain their public preparation, duration and empty worker-prefix restrictions.
The broader [`Caller.prepared_protocol_sequence_soundness`](../../UnifiedReduced/Theorems.lean)
supports explicit LUI restarts between compression spans in one continuous mixed
history. Raw matching derives masks within each controller region; earlier workers
remain in the prefix. Every extended-round worker must belong to one such region,
and each region retains its local ten-position cap. Complete span counts, durations,
mode/flags and literal preparation remain explicit; completion alone never restarts.

[`Call.execution_soundness`](ReferenceCalls.lean) now supplies a sequence of
[complete independent round calls](../../../Circuits/Blake2Round/Call.lean) in the
actual full Sail states, with exact writes/frame and shared terminal mapping.
The existing public mode/count and initialized history derive the whole x12
word, exclusive round, all three mode flags and pointer ABI. The completed
ten-round controller is rejected by the successful-call reference. Modeled-table
fidelity and the RAM domain remain explicit. [Full mixed execution](../../UnifiedReduced/FullExecution.lean)
now connects caller fetch/PC retirement under the temporary occurrence ledger;
its implementation enforcement remains open under F03.
