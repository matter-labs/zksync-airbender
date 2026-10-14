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
[`ProgramCallerRegion`](WindowSchedule.lean) describes public code in a PC/clock
interval: ordinary entries lie outside it and CSR entries select its full family.
With a sequential ordinary registry, accepted state/request matching derives
[`ProgramCallerWindow`](WindowSchedule.lean): every selected machine row is a
caller, both row counts equal `(upper - lower) / 4`, and every selected worker has
that public family and a unique native slot. No selected-worker family, count or
duration proportional to its row list is supplied. See
[`Caller.program_window_schedule_soundness`](../../Trace/UnifiedReduced/Theorems.lean).
Alignment, cut location and the public code profile remain explicit. COPY followed
by ADDI checks this connection; the wrong family and an interval including the
ordinary instruction are rejected. Both invalid bigint controls remain admitted
by this request/schedule result.

[`WrappedProgramCallerRegion`](WindowSchedule.lean) gives the corresponding
public policy at modular RV32 addresses. At every clock inside the interval,
ordinary entries are excluded and matching full CSR entries select the family.
Addresses are relative to the supplied native initial PC/clock, as in the linear entry.
Accepted decoding and state/clock matching derive actual participation, counts,
unique requests and native slots through
[`Caller.wrapped_program_window_schedule_soundness`](../../Trace/UnifiedReduced/Theorems.lean).
This entry uses the aligned sequential/comparison registry, modeled setup and
minimum modulus 4194304. It needs no PC injectivity or no-wrap premise. COPY
checks nonempty family/count binding and rejection of wrong family/ordinary code;
the SLTIU-wrap fixture rejects a selected ADDI at zero and admits the empty cut.

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
[`WrappedSequentialProgram`](ControlPreparation.lean) separately adds the four
original comparisons and public code alignment. Its preparation entry retains
modeled setup and `4194304 ≤ p`. [`wrapped_program_pc_advance` and
`wrapped_program_pc_clock`](../../../Proofs/UnifiedReduced/ControlPreparation.lean)
derive modular RV32 successors and program addresses from accepted native
constraints, public decoding and state/clock matching. Comparison cleanup/carry
values are derived; neither wrap flags nor successors are supplied.
Selected caller/controller regions and global public round-CSR occurrence
coverage also support this modular registry; jumps and branches remain outside
both preparation profiles.
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

[Successive preparation regressions](../../../../Tests/ControlPreparation.lean)
check actual x12 values 65537→128→0 with reversed row order, retained write clocks,
one connected history across both preparation cuts, and rejection of a wrong
literal or fabricated second read.
The [arithmetic preparation regression](../../../../Tests/ControlPreparation.lean)
uses an aliased ADD before ADDI-from-x0, with reversed native rows. One continuous
history derives actual x12 values 65537→131074→0, retaining write clocks six/ten;
a fabricated preparation read is rejected by joint matching.
[`triadd_prefix_and_preparation_share_history`](../../../../Tests/ControlPreparation.lean)
checks the custom prefix with the same aliased fixture: actual x12 is
65537→196611→0, with the same clocks and fabricated-read rejection. This is
preparation and memory transport. It adds no successful full-prefix retirement
claim and does not remove the discarded-LW profile boundary.
The [wrapped comparison regression](../../../../Tests/UnifiedComparison.lean)
places SLTIU at `0xfffffffc` and ADDI-from-x0 at zero, with reversed native rows.
One continuous history derives actual x12 = 65537→1→0, retains clocks six/ten
and rejects a fabricated reset read, wrong literal and misaligned public code.
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

[`ProgramRoundRegionInputs`](../../Trace/UnifiedReduced/PreparedRoundWindows.lean)
replaces local round-worker shape with public CSR regions, aligned ordered cuts
and an extent of at most forty ticks. Accepted matching derives the selected
family/count, ten-position bound and exact duration through
[`Caller.program_round_region_soundness`](../../Trace/UnifiedReduced/Theorems.lean).
[`ProgramPreparedProtocolInputs`](../../Trace/UnifiedReduced/PreparedRoundWindows.lean)
uses these derived regions for mask transport and continuous reference composition.
Global coverage stays explicit; live request matching does not rule out surplus
zero-clock workers. Empty prepared regions retain clock-six LUI tokens, wrong
flags/family and invalid cuts are rejected, and the unissued G-prefix fixture
remains admitted by the stronger context.

[`WrappedProgramRoundRegionInputs` and `WrappedProgramPreparedProtocolInputs`](../../Trace/UnifiedReduced/PreparedRoundWindows.lean)
extend these local shape derivations to modular code regions. Public preparation
and at most forty ticks derive each controller's family, ten-position bound and
duration. [`Caller.wrapped_program_prepared_protocol_sequence_soundness`](../../Trace/UnifiedReduced/Theorems.lean)
then reuses the existing raw-mask and complete-reference composition on the same
continuous history. Selected spans retain public reference duration and cuts;
global extended-round worker coverage remains explicit. Both bigint-control gaps
and the actual unissued G-prefix effect remain accepted by the new inputs/conversion.

[`ProgramRoundCallerCoverage`](../../Trace/UnifiedReduced/PreparedRoundWindows.lean)
places public decoded round CSRs in the prepared regions. Accepted native matching
then derives every live round worker's membership and its converse through
[`Caller.program_round_coverage_soundness`](../../Trace/UnifiedReduced/Theorems.lean).
[`Caller.program_round_live_masks_soundness`](../../Trace/UnifiedReduced/Theorems.lean)
then derives exclusive masks for all issued round workers from public LUI preparation
and raw joint matching, using the public memory context without full worker coverage.
[`Caller.program_round_global_coverage_boundary_soundness`](../../Trace/UnifiedReduced/Theorems.lean)
proves that full coverage is equivalent to the absence of zero-clock extended-round
workers within this public sequential/controller profile. Neither coverage theorem
assumes worker coverage or nonzero invocation. Global mask transport still needs full
coverage; unissued G workers remain admitted with their actual prefix effects.

[`WrappedProgramRoundCallerCoverage`](../../Trace/UnifiedReduced/PreparedRoundWindows.lean)
requires coverage at every aligned modular occurrence between supplied native
clock endpoints. Strict clock increments and matching derive actual caller bounds,
so repeated addresses need no injectivity assumption. The modular coverage,
issued-mask and global-boundary entry points in
[unified trace review](../../Trace/UnifiedReduced/README.md) prove the corresponding
results with modeled setup and the aligned comparison registry. Unissued round
masks/exclusion remain open. A repeated-address public-policy regression rejects
covering only one occurrence; empty prepared cuts and the actual unissued G worker
remain admitted.

The native domain, public program, protocol counts and existing prefix scope
remain explicit. These helpers do not claim whole mixed caller retirement.
Follow [unified trace review](../../Trace/UnifiedReduced/README.md) for actual conclusions.
