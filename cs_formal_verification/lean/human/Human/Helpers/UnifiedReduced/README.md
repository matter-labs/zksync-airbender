# Unified-machine shared context

This directory defines shared context for the unified machine artifact, including
its public program, native layout and joint histories with all worker families. It
states fetch/request matching and the input contracts for mixed memory,
native-clock windows and control preparation. These are the inputs and
interpretations used by execution claims, rather than whole-execution conclusions.

## Checked connections

[`Caller.rv_mixed_memory_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean)
derives actual register/RAM transfers on an `RV.State`, ranges, addresses and worker reference effects
from one joint machine/worker history. It does not require a separate worker
permutation or supplied intermediate states.

Accepted clock/state matching also derives instruction counts and caller regions
between public cuts; actual cut states and retained worker boundaries follow.
[Unified trace results](../../Trace/UnifiedReduced/README.md#checked-results)
link the scheduling, projection, control-preparation and reference claims.
Public cut/duration, program/domain and protocol conditions remain explicit.

[Registry](Registry.lean) connects the machine row to its imported layout.
[RVProgram](RVProgram.lean) and [RVExecutionInputs](RVExecutionInputs.lean) name the public program
(`RV.read` of the ROM image, `RV.decode`) and boot inputs (`RVBootInputs`: seeds from the inline
inits/teardowns sets, the modeled setup table fixed by the ROM image). There is no machine-configuration
or code-domain premise.

[RVRequestTrace](RVRequestTrace.lean) and [WorkerProjection](../Delegation/WorkerProjection.lean)
connect full caller requests to workers. [RVMixedMemory](RVMixedMemory.lean) retains
machine ports and all worker families in the same history; fetch is bound to the current state by
`RVCycleFetch` ([RVCallerCycles](../../Trace/UnifiedReduced/RVCallerCycles.lean)).

[RVWindows](RVWindows.lean) describes native-clock cuts and selected regions.
`RVProgramCallerRegion` describes public code in a PC/clock
interval: ordinary entries lie outside it and CSR entries select its full family.
With a sequential ordinary registry, accepted state/request matching derives
`RVProgramCallerWindow`: every selected machine row is a
caller, both row counts equal `(upper - lower) / 4`, and every selected worker has
that public family and a unique native slot. No selected-worker family, count or
duration proportional to its row list is supplied. See
[`Caller.rv_program_window_schedule_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean).
Alignment, cut location and the public code remain explicit. Bigint control validity is not checked by this
request/schedule result.

[RVControlPreparation](RVControlPreparation.lean) names the public preparation registry.
It accepts one uniform literal, different ADDI-from-x0/LUI literals, or ordinary
arithmetic, LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT forms along a
straight path with callers. `RVSequentialProgram` states
these original public instruction forms (in terms of `RV.decode`); `RVArithmeticProgram` remains available.
No operand, read, native selector or result is supplied.
[`rv_sequential_fields_mask`, `rv_sequential_program_pc_advance` and
`rv_sequential_program_pc_clock`](../../../../slop/Slop/UnifiedReduced/RVCaller/ControlPreparation.lean)
derive native selectors, PC increments and the instruction address from public
decoding and accepted constraints/matching. Jumps, branches and comparisons are
outside this linear PC/clock profile.
The final preparation instruction must still be the specified public literal.
Its address follows from matching, without a selected-row or control-read premise.
Only its final cycle is worker-free; earlier worker effects remain in the same
history. The original extended-round first-span scope retains an empty worker prefix.
Boundary timestamps are retained; scheduling, actual controls and intermediate
states are derived rather than supplied.
The prepared control window
connects two prepared controls through the same actual intervening history, keeping
all ordinary and worker accesses. Both controls follow from the public registry
and joint prefix/window matching.

The native window chain and sequence ([RVMixedWindows](../../Trace/UnifiedReduced/RVMixedWindows.lean)) execute
any ordered finite list of windows and their gaps continuously from the retained boundaries;
complete [prepared G/Keccak references](../../Trace/UnifiedReduced/RVPreparedHashWindows.lean) use
those exact segment states and derive their references without supplied intermediate states.
Each span retains its public preparation and protocol ABI.
[Prepared controller regions](../../Trace/UnifiedReduced/RVPreparedRoundWindows.lean)
derive extended-BLAKE masks inside each public LUI-prepared caller window
before the values are transported. Earlier workers remain in history; each region has its own
ten-position cap. The broader protocol entry requires those regions to cover
every extended-round worker, then binds complete G/extended-BLAKE/Keccak lists to
the same continuous execution. Coverage and each span's preparation/count/duration
remain explicit; no mask, control read or intermediate state is supplied.
[Overlapping or unaligned window sequences](../../../../test/Tests/ControlPreparation.lean) are rejected.

The native domain, public program, protocol counts and existing prefix scope
remain explicit. These helpers do not claim whole mixed caller retirement.
Follow [unified trace review](../../Trace/UnifiedReduced/README.md) for actual conclusions.
