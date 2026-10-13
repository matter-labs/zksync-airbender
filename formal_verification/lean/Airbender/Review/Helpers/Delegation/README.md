# Shared caller and worker context

This directory models caller requests and native worker rows in shared initialized
histories. Request tokens identify the CSR family and invocation; memory and
operation contexts interpret worker observations, while span/window inputs state
protocol and boundary conditions. Logical matching alone does not establish valid
caller controls or full CSR semantics.

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
