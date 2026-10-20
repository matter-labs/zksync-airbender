# Unified-machine shared context

This directory defines shared context for the unified machine artifact, including
its public program, native layout and joint histories with all worker families. It
states fetch/request matching and the input contracts for mixed memory,
native-clock windows and control preparation. These are the inputs and
interpretations used by execution claims, rather than whole-execution conclusions.

## Checked connections

[`Caller.mixed_memory_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/Theorems.lean)
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
[`ProgramCallerRegion`](WindowSchedule.lean) describes public code in a PC/clock
interval: ordinary entries lie outside it and CSR entries select its full family.
With a sequential ordinary registry, accepted state/request matching derives
[`ProgramCallerWindow`](WindowSchedule.lean): every selected machine row is a
caller, both row counts equal `(upper - lower) / 4`, and every selected worker has
that public family and a unique native slot. No selected-worker family, count or
duration proportional to its row list is supplied. See
[`Caller.program_window_schedule_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/Theorems.lean).
Alignment, cut location and the public code profile remain explicit. COPY followed
by ADDI checks this connection; the wrong family and an interval including the
ordinary instruction are rejected. Both invalid bigint controls remain admitted
by this request/schedule result.

[ControlPreparation](ControlPreparation.lean) names the public preparation registry.
It accepts one uniform literal, different ADDI-from-x0/LUI literals, or ordinary
arithmetic, LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT forms along a
straight path with callers. [`SequentialProgram`](ControlPreparation.lean) states
these original public instruction forms; `ArithmeticProgram` remains available.
No operand, read, native selector or result is supplied.
[`sequential_fields_mask`, `sequential_program_pc_advance` and
`sequential_program_pc_clock`](../../../Proofs/UnifiedReduced/ControlPreparation.lean)
derive native selectors, PC increments and the instruction address from public
decoding and accepted constraints/matching. Jumps, branches and comparisons are
outside this linear PC/clock profile; comparisons use a wraparound PC path.
The final preparation instruction must still be the specified public literal.
Its address follows from matching, without a selected-row or control-read premise.
Only its final cycle is worker-free; earlier worker effects remain in the same
history. The original extended-round first-span scope retains an empty worker prefix.
Boundary timestamps are retained; scheduling, actual controls and intermediate
states are derived rather than supplied.
The [prepared control window](../../Trace/UnifiedReduced/ControlPreparation.lean)
connects two prepared controls through the same actual intervening history, keeping
all ordinary and worker accesses. Both controls follow from the public registry
and joint prefix/window matching.

[Successive preparation regressions](../../../../test/Tests/ControlPreparation.lean)
check actual x12 values 65537→128→0 with reversed row order, retained write clocks,
one connected history across both preparation cuts, and rejection of a wrong
literal or fabricated second read.
The [arithmetic preparation regression](../../../../test/Tests/ControlPreparation.lean)
uses an aliased ADD before ADDI-from-x0, with reversed native rows. One continuous
history derives actual x12 values 65537→131074→0, retaining write clocks six/ten;
a fabricated preparation read is rejected by joint matching.
[`triadd_prefix_and_preparation_share_history`](../../../../test/Tests/ControlPreparation.lean)
checks the custom prefix with the same aliased fixture: actual x12 is
65537→196611→0, with the same clocks and fabricated-read rejection. This is
preparation and memory transport. It adds no successful full-prefix retirement
claim and does not remove the discarded-LW profile boundary.
The [native window chain](../../Trace/UnifiedReduced/MixedWindows.lean) also executes
two windows and their gap continuously from those retained boundaries. Complete
[prepared G/Keccak chains](../../Trace/UnifiedReduced/PreparedHashWindows.lean) use
that same execution and derive both references without supplied intermediate states.
The same [sequence mapping](../../Trace/UnifiedReduced/MixedWindows.lean) now
connects any ordered finite list of windows and gaps. A nonempty list of complete
[prepared references](../../Trace/UnifiedReduced/PreparedHashWindows.lean) uses
those exact segment states; each span retains its public preparation and protocol ABI.

[Prepared controller regions](../../Trace/UnifiedReduced/PreparedRoundWindows.lean)
now derive extended-BLAKE masks inside each public LUI-prepared caller window
before Sail transport. Earlier workers remain in history; each region has its own
ten-position cap. The broader protocol entry requires those regions to cover
every extended-round worker, then binds complete G/extended-BLAKE/Keccak lists to
the same continuous execution. Coverage and each span's preparation/count/duration
remain explicit; no mask, control read or intermediate state is supplied.

The native domain, public program, protocol counts and existing prefix scope
remain explicit. These helpers do not claim whole mixed caller retirement.
Follow [unified trace review](../../Trace/UnifiedReduced/README.md) for actual conclusions.
