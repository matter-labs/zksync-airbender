# Shared caller and worker context

This directory models caller requests and native worker rows in shared initialized
histories. Request tokens identify the CSR family and invocation; memory and
operation contexts interpret worker observations, while span/window inputs state
protocol and boundary conditions. Logical matching alone does not establish valid
caller controls or full CSR semantics.

## Checked connections

For the four worker families, imported constraints and initialized full-token
matching imply native clock/address bounds, strict per-cell ordering and Clean
memory consistency; [`rv_memory_soundness`](../../../../proven/Proven/Final/Trace/Delegation/RVTheorems.lean)
states this, and [`labeled_history`](../../../../proven/Proven/Delegation/History.lean)
constructs the history. The corresponding
[`rv_native_memory_execution`](../../../../proven/Proven/Final/Trace/Delegation/RVTheorems.lean) realizes actual
`RV.State` register/RAM reads and writes and terminal cells under the public alignment/domain conditions;
RAM cells include the shadow RAM below `ROM_END` (`RV.State.delegationRAM`).

[Caller composition](../../Trace/Delegation/README.md#checked-results) additionally
derives issued-worker placement and shared histories. The
[logical memory explanation](../Memory/README.md#logical-memory-result) describes
why matching imposes history. It does not require valid bigint controls or exclude
surplus zero-clock effects to make that core memory implication true.

Start with [Columns](Columns.lean), [Requests](Requests.lean), [CallerRequests](CallerRequests.lean) and [Decoder](Decoder.lean)
to identify the caller token, full CSR family and imported worker observables.
[RVRequestTrace](RVRequestTrace.lean) and [RVRequestEffects](RVRequestEffects.lean)
state logical request matching and context; matching does not establish the full CSR ABI.

[RVMemory](RVMemory.lean), [RVSharedMemory](RVSharedMemory.lean) and [RVMixedMemory](RVMixedMemory.lean)
describe the initialized native pools ([Memory](Memory.lean), [SharedMemory](SharedMemory.lean) and
[MixedMemory](MixedMemory.lean) hold the shared definitions). [WorkerContext](WorkerContext.lean)
exposes actual per-port observations. [RVOperations](RVOperations.lean) selects the existing local worker references.

[RVSpanABI](RVSpanABI.lean), [NativeWindows](NativeWindows.lean) and
[RequestWindows](RequestWindows.lean) give protocol and native-cut inputs. [RVSchedule](RVSchedule.lean)
states the caller-cycle placement of issued workers.
Schedules and intermediate values must follow from accepted history and matching.

Keep zero-clock surplus-worker effects and the issued bigint invalid-control fixture
at their actual logical scope. They remain admitted by
the relevant input relations; no assumed ABI validity closes them.
[Trace/Delegation](../../Trace/Delegation/README.md) owns execution and composition.

The machine targets use the delegation spec for undefined controls and worker pointer use, without a validity premise.
The [valid-use claims](../../ISA/ValidUse/Theorems.lean) give the independent BLAKE2s, Keccak and bigint references for aligned, distinct RAM buffers and valid controls.
