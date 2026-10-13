# Unified-machine shared context

This directory defines shared context for the unified machine artifact, including
its public program, native layout and joint histories with all worker families. It
states fetch/request matching and the input contracts for mixed memory,
native-clock windows and control preparation. These are the inputs and
interpretations used by execution claims, rather than whole-execution conclusions.

## Checked connections

[`Caller.mixed_memory_soundness`](../../Trace/UnifiedReduced/Theorems.lean)
derives actual GPR/RAM transfers, ranges, addresses and worker reference effects
from one joint machine/worker history. It does not require a separate worker
permutation or supplied intermediate states.

Accepted clock/state matching also derives instruction counts and caller regions
between public cuts; actual cut states and retained worker boundaries follow.
[Unified trace results](../../Trace/UnifiedReduced/README.md#checked-results)
link the scheduling, projection, control-preparation and reference claims.
Public cut/duration, program/domain and protocol conditions remain explicit.

[Registry](Registry.lean) connects the machine row to its imported layout.
[Program](Program.lean), [ExecutionInputs](ExecutionInputs.lean) and
[CustomInputs](CustomInputs.lean) name the public decoder/initialization/profile inputs.
[NativeROM](NativeROM.lean) exposes the ordinary-machine ROM view.

[RequestTrace](RequestTrace.lean) and [WorkerProjection](WorkerProjection.lean)
connect full caller requests to workers. [MixedMemory](MixedMemory.lean) retains
machine ports and all worker families in the same history; [MixedFetch](MixedFetch.lean)
binds current-state fetch.

[Windows](Windows.lean), [WindowProjection](WindowProjection.lean) and
[WindowSchedule](WindowSchedule.lean) describe native-clock cuts and selected regions.
[ControlPreparation](ControlPreparation.lean) names the public preparation registry.
It accepts either one uniform literal or different ADDI-from-x0/LUI literals along
a straight path with callers. Native PC/clock matching identifies the public
instruction at each preparation cut, without a selected-row or control-read premise.
Only its final cycle is worker-free; earlier worker effects remain in the same
history. The extended-round scope separately retains an empty worker prefix.
Boundary timestamps are retained; scheduling, actual controls and intermediate
states are derived rather than supplied.
The [prepared control window](../../Trace/UnifiedReduced/ControlPreparation.lean)
connects two prepared controls through the same actual intervening history, keeping
all ordinary and worker accesses. Both controls follow from the public registry
and joint prefix/window matching.

[Successive preparation regressions](../../../../Tests/ControlPreparation.lean)
check actual x12 values 65537→128→0 with reversed row order, retained write clocks,
one connected history across both preparation cuts, and rejection of a wrong
literal or fabricated second read.

The native domain, public program, protocol counts and existing prefix scope
remain explicit. These helpers do not claim whole mixed caller retirement.
Follow [unified trace review](../../Trace/UnifiedReduced/README.md) for actual conclusions.
