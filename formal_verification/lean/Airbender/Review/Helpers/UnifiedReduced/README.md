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
[`PCRelativePreparation`](PCRelativePreparation.lean) separately identifies a final
original AUIPC through that same modular sequential/comparison registry. Its
[`pcRelativeControl`](PCRelativePreparation.lean) computes the RV32 sum of the
derived public instruction address and the decoded U-immediate. Native selector,
carry and overflow equations derive the canonical result; initialized matching
retains its actual write token at cut minus two. Only the final cycle is
worker-free, so earlier issued/unissued effects remain. No row selector, desired
control value or operand read is an input. This preparation/memory entry retains
modeled setup/tables and the existing extended-round ABI. The
[computed hash-window source](../../Trace/UnifiedReduced/ComputedHashWindows.lean)
now connects literal, publicly placed AUIPC or literal→ADDI preparation to complete selected
G/Keccak references and ordered lists in one continuous history. Public code
placement must compute the protocol entry constant; its actual read is derived.
Selected family/count/duration, nonround scope and logical matching stay explicit.
The new public modular-region entry derives caller rows, exact request slots,
worker family/count and complete window/list composition for each source.
Public mode/code/duration, nonround scope and logical matching remain explicit.
The separate [source-aware round regions](../../Trace/UnifiedReduced/ComputedRoundRegions.lean)
derive actual round-zero seeds and exclusive regional masks; public modular
controller extents derive local shape, while global memory keeps full round
coverage explicit. Source-aware public round-CSR occurrence coverage now derives
precisely live membership and masks, retaining the zero-clock coverage boundary.
Complete G, extended-BLAKE and Keccak lists also admit all public sources; public
modular caller/controller regions derive shape before the existing continuous
history composition. Full round coverage stays explicit. Broader operand-dependent
preparation and jumps/branches remain separate. Concrete fixtures use PC four to produce 524292 and
PC 65540 with immediate 0xfffff to wrap the sum to 61444; both retain clock six.

The separate [register-dependent ADDI scope](RegisterPreparation.lean) derives an
actual operand state from initialized history and a public final instruction.
Memory induction derives bounds and native arithmetic derives its signed-immediate
RV32 sum. The [execution result](../../Trace/UnifiedReduced/RegisterPreparation.lean)
retains the actual native cycle, matching and canonical output token at cut minus
two, including aliases and earlier issued/unissued effects. No desired operand
or result is supplied. Only the final cycle is worker-free; domain/setup/tables
and the round-mask boundary remain explicit. Native fixtures retain clock six
and actual 65537→65665, 65537→65536 and unissued-prefix 0→1→1 states, rejecting
wrong immediates and fabricated source reads.

The same file's `LiteralAddiPreparation` identifies two consecutive public
instructions: a literal writes the source, then ADDI consumes it. Initialized
prefix/suffix matching, strict clocks and the existing distinct public domain
derive the actual first-read token, before Sail transport or regional round-mask
derivation. A public equation on the literal/immediate binds the result to a
protocol entry constant. This third
[hash preparation source](../../Trace/UnifiedReduced/ComputedHashWindows.lean)
feeds the existing complete G/extended-BLAKE/Keccak windows and lists, retaining
all coverage/domain/setup/table and logical-matching boundaries. Only the two
final cycles are worker-free. Native reversed-row fixtures derive
65537→127→128 and 65537→129→128 with aliases, signed −1 and canonical clock ten;
wrong constants/immediates, fabricated reads and incomplete references are
rejected. An accepted unissued G prefix remains before literal zero and ADDI
128. Full reference claims are general accepted-witness theorems; concrete
fixtures cover preparation and empty-region guards. Other gap instructions,
broader operations and complete Sail retirement remain separate.


The [finite register-chain scope](RegisterChains.lean),
`PublicRegisterPreparation`, extends literal/AUIPC roots with consecutive ADDIs
across nonzero registers or aliases. Its indexed value follows the public instruction
expression. Raw prefix/suffix matching, strict clocks and the existing distinct
public domain derive each actual operand token by induction. This precedes Sail
transport and round-mask derivation and reuses the two-step token proof. Only
selected preparation cycles are worker-free; earlier effects remain. The
[chain execution](../../Trace/UnifiedReduced/RegisterChains.lean) retains one
initialized prefix, the actual cut read and canonical final token. The same
source feeds all complete selected-reference windows/lists with their existing
boundaries. Native three-instruction fixtures retain actual x12 = 127/129,
x10 = 128 and final x12 = 128, clock fourteen, negative immediates and reversed
rows; malformed operands/instructions/constants and incomplete references are
rejected. AUIPC root fixtures and the actual unissued prefix remain inhabited.
Other gap instructions, broader operations and complete Sail retirement remain
separate.


The [public dataflow scope](RegisterDataflow.lean), `PublicRegisterDataflow`, adds
intervening arithmetic, bitwise/shift/REV8, comparison and admitted TRIADD/XORROT
writes to other nonzero GPRs.
`RegisterFramePreparation` and `BinaryRegisterWrite` bind the destination using
the original public instruction constructor and successful decoding, including
supported RV32 shift-payload checks. `ArithmeticFramePreparation` retains its
original contract as a special case. Native decoding derives its GPR bank/index without
operand bounds or arithmetic results. The original ADDI scope remains a special
case. A gap can read and refresh the tracked
register; original public decoding derives its separate destination. Raw matching
and readonly-port preservation derive the value, retaining the actual timestamp
and all other writes. Induction combines these gaps with computed ADDIs before
Sail transport or regional masks. No inert-gap or desired read/state/bound/selector
is supplied. The [dataflow execution](../../Trace/UnifiedReduced/RegisterDataflow.lean)
retains exact prefix matching and actual boundary tokens; after a gap they need
not be at cut minus two.
A final public ADDI derives that fresh canonical output for the existing complete
selected-reference windows/lists with their unchanged explicit boundaries. Only
selected ordinary cycles are worker-free; caller gaps retain their workers. Native reversed-row
fixtures derive x12 = 127/129, gap x10 = 127/129 from initial 65537 and final
x12 = 128. The readonly refresh retains clock eight and final output clock
fourteen; a fabricated clock ten passes local native constraints/timestamps but
fails architectural matching. Wrong constants and incomplete references are
rejected; the actual unissued G-prefix effect remains. New native ADD/SUB gaps
read x12 twice, preserve 127/129, write x10 = 254/0 and retain the second refresh
at clock nine before final x12 = 128 at clock fourteen. Wrong public destination
and instruction forms are rejected. A stale clock-eight source satisfies local
constraints/timestamp queries but fails global matching by double consumption.
Native XOR/AND gaps also check two aliased reads, x12 = 127/129, real x10 = 0/129
writes, clock-nine refreshes and final x12 = 128 at clock fourteen. Stale sources
remain locally valid and globally rejected; wrong public destinations/forms,
illegal shifts and discarded binary destinations are rejected.
`ComparisonRegisterWrite` covers all four original comparisons;
`CustomRegisterWrite` covers TRIADD and the four pinned XORROT forms. Their native
GPR footprint follows from the original public constructor and decoding, without
operands, predicate bits or results. Native SLTU/TRIADD gaps preserve x12 = 127/129,
write x10 = 0/65795, retain clock-nine refreshes and derive final x12 = 128.
TRIADD reads actual old x10 = 65537. Stale sources, wrong public destinations/
forms, unsupported MOPs and discarded selected destinations are checked at the
existing local/matching/registry boundaries. Pinned custom clauses remain
unchanged; no full custom retirement or Zimop fallback is asserted.
`LoadFramePreparation` and `StoreFramePreparation` derive the native GPR/RAM
footprint from original public decoding, without addresses, loaded values or store
results as inputs. LW includes discarded destinations as native NOPs; SW derives
RAM/GPR bank separation. Raw initialized matching preserves the tracked value
while retaining every real load/store/refresh. Native RAM fixtures derive
x10 = 4194304→42 and RAM = 42→129, exact clocks six/nine/ten and final x12 = 128
at clock fourteen. A discarded misaligned LW-to-x0 is admitted with only x0 gap
accesses and a program failing NoDiscardedLoads; the tracked literal and RAM
retain clocks six/zero. Fabricated source clocks and RAM reads satisfy local
constraints/timestamps but fail global matching. Wrong public load destinations
and store sources are rejected. Original discarded-load and native ROM-shadow
boundaries stay explicit; no original memory-clause retirement is added.
`CallerFramePreparation` extends `PublicRegisterDataflow` with caller gaps.
Caller gaps now preserve tracked GPRs outside x10/x12. Public modular code
excludes ordinary entries at the selected address; accepted decoding and PC/clock
matching derive the caller. The original imported port descriptors derive the
write footprint of all four worker layouts: bigint/BLAKE can write x12, Keccak
can write x10, and other fixed-register accesses only refresh values. RAM writes
remain in the same initialized history. No worker-free gap, selected worker,
valid control, nonzero invocation, desired read or inert effect is an input.
The raw token induction feeds the existing final ADDI and complete selected-reference
interfaces, retaining their domain/setup/table, coverage and matching boundaries.
A [reversed-row literal→COPY→ADDI fixture](../../../../Tests/UnifiedDelegation.lean) derives x13 = 0→127→127 while COPY
changes actual x12 = 128→0; final ADDI restores x12 = 128 at clock fourteen.
The tracked x13 token retains clock six, and the actual x11 pointer refresh retains
clock eleven. A fabricated clock-eleven x13 source satisfies local constraints and
timestamps but fails initialized matching. Both issued invalid bigint controls
also retain the x11 refresh law; ordinary-code gaps and incomplete reference
windows are rejected. Zero-clock prefix effects, ROM-shadow transport and discarded
loads keep their existing scope. This proves memory preparation, not full custom
CSR retirement. Worker writes to the tracked x10/x12 and broader operands remain
open; they are not assumed to preserve values.


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
results with modeled setup and the aligned comparison registry. General supported
masks and exclusion for unissued rounds remain open. A repeated-address public-policy regression rejects
covering only one occurrence; empty prepared cuts and the actual unissued G worker
remain admitted.

The [unissued worker entry](../../Trace/UnifiedReduced/UnissuedWorkers.lean) now
roots all zero-clock worker reads directly in public initialization. Native clocks
and strict memory order derive the write floor; an extra initial-clock floor and
supported-operation premises are absent. For an unissued extended-round worker,
the actual public x12 seed characterizes each exclusive mask exactly. Unsupported
zero/multibit encodings remain outside the ABI, and the actual G prefix update
remains admitted. This classification does not establish worker exclusion or
inertness and does not construct an accepted unissued-round witness.
The [full worker-clock entry](../../Trace/UnifiedReduced/Theorems.lean) also uses
the actual fixed x10 transfer shared by all four layouts to derive numeric and
raw invocation-clock uniqueness from initialized architectural matching. A
distinct physical-cell domain bounds the unissued sublist to at most one
occurrence. Two identical unissued G rows retain native/request checks but fail
architectural acceptance; the existing single G worker attains the bound, with
its actual effect retained. Both invalid bigint controls remain admitted. No
supported-mask or nonzero-invocation premise supplies this uniqueness.

The native domain, public program, protocol counts and existing prefix scope
remain explicit. These helpers do not claim whole mixed caller retirement.
Follow [unified trace review](../../Trace/UnifiedReduced/README.md) for actual conclusions.
