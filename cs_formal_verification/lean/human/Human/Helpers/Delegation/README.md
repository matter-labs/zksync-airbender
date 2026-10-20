# Shared caller and worker context

This directory models caller requests and native worker rows in shared initialized
histories. Request tokens identify the CSR family and invocation; memory and
operation contexts interpret worker observations, while span/window inputs state
protocol and boundary conditions. Logical matching alone does not establish valid
caller controls or full CSR semantics.

## Checked connections

For the four worker families, imported constraints and initialized full-token
matching imply native clock/address bounds, strict per-cell ordering and Clean
memory consistency; [`memory_soundness`](../../../../slop/Slop/Final/Trace/Delegation/Theorems.lean)
states this, and [`labeled_history`](../../../../slop/Slop/Delegation/History.lean)
constructs the history. The corresponding
[`native_memory_execution`](../../../../slop/Slop/Final/Trace/Delegation/Theorems.lean) realizes actual
Sail reads/writes and terminal cells under the public alignment/domain conditions.

[Caller composition](../../Trace/Delegation/README.md#checked-results) additionally
derives issued-worker placement and shared histories. The
[logical memory explanation](../Memory/README.md#logical-memory-result) describes
why matching imposes history. It does not require valid bigint controls or exclude
surplus zero-clock effects to make that core memory implication true.

Start with [Columns](Columns.lean), [Requests](Requests.lean) and [Decoder](Decoder.lean)
to identify the caller token, full CSR family and imported worker observables.
[RequestTrace](RequestTrace.lean) and [RequestEffects](RequestEffects.lean)
state logical request matching and context; matching does not establish the full CSR ABI.

[Memory](Memory.lean), [SharedMemory](SharedMemory.lean) and [MixedMemory](MixedMemory.lean)
describe the initialized native pools. [WorkerContext](WorkerContext.lean)
exposes actual per-port observations. [Operations](Operations.lean) and
[SharedOperations](SharedOperations.lean) select the existing local worker references.

[SpanABI](SpanABI.lean), [NativeWindows](NativeWindows.lean) and
[RequestWindows](RequestWindows.lean) give protocol and native-cut inputs.
Schedules and intermediate values must follow from accepted history and matching.

Keep zero-clock surplus-worker effects, issued bigint invalid-control fixtures
and worker ROM shadows at their actual logical scope. They remain admitted by
the relevant input relations; no assumed ABI validity closes them.
[Trace/Delegation](../../Trace/Delegation/README.md) owns execution and composition.
