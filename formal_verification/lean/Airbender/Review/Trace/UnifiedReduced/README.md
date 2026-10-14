# Unified execution review

This directory states execution claims for the unified artifact: ordinary and
selected custom instruction retirement, caller-cycle observations, and complete
reference effects on selected native-clock windows. The claims share actual
history-derived states but use different registries and input contracts; full
mixed execution with delegation callers remains a separate obligation.

## Checked results

| Result from accepted history and stated public inputs | Direct theorem in Theorems |
| --- | --- |
| Original standard instructions retire and reach native terminal PC/cells, using public ROM bytes. | [`execution_soundness`](Theorems.lean) |
| Standard instructions plus TRIADD/XORROT retire together; delegation callers are outside the registry. | [`Mixed.execution_soundness`](Theorems.lean) |
| Machine and worker reads/writes, bounds and references share one actual initialized history. | [`Caller.mixed_memory_soundness`](Theorems.lean) |
| Exact caller regions, counts and slots follow from state/request matching and public cuts/duration. | [`Caller.window_schedule_soundness` and `Caller.request_window_soundness`](Theorems.lean) |
| Public sequential code identifies caller regions; native matching derives selected worker family, counts and slots. | [`Caller.program_window_schedule_soundness`](Theorems.lean) |
| Modular public code regions derive the same selected family/count/request-slot binding through comparison wraparound. | [`Caller.wrapped_program_window_schedule_soundness`](Theorems.lean) |
| Public CSR controller regions and at most forty ticks derive round-worker family/count/duration and the ten-position bound. | [`Caller.program_round_region_soundness`](Theorems.lean) |
| Modular public controller regions derive local round-worker shape with the same forty-tick extent. | [`Caller.wrapped_program_round_region_soundness`](Theorems.lean) |
| Coverage of public decoded round CSRs derives region membership exactly for live round workers. | [`Caller.program_round_coverage_soundness`](Theorems.lean) |
| Public round CSR coverage and LUI preparation derive every issued round mask from raw matching, without full worker coverage. | [`Caller.program_round_live_masks_soundness`](Theorems.lean) |
| Full controller coverage is equivalent to absence of zero-clock extended-round workers in the public sequential/controller profile. | [`Caller.program_round_global_coverage_boundary_soundness`](Theorems.lean) |
| Modular public round-CSR occurrence coverage derives membership exactly for live round workers, including repeated addresses. | [`Caller.wrapped_program_round_coverage_soundness`](Theorems.lean) |
| Modular occurrence coverage and public preparation derive every issued round mask without full worker coverage. | [`Caller.wrapped_program_round_live_masks_soundness`](Theorems.lean) |
| The modular profile exposes the same equivalence between full coverage and absence of zero-clock round workers. | [`Caller.wrapped_program_round_global_coverage_boundary_soundness`](Theorems.lean) |
| Actual joint cut states and projected worker boundaries retain native timestamps. | [`Caller.mixed_window_soundness` and `Caller.mixed_window_projection_soundness`](Theorems.lean) |
| Aligned public sequential/comparison decoding and native matching derive modular RV32 program addresses, including comparison PC wraparound. | [`Caller.wrapped_program_address_soundness`](Theorems.lean) |
| Public ADDI-from-x0/LUI preparation yields actual controls after literal, sequential ordinary/custom or aligned comparison prefixes; native PC/clock matching derives each preparation address. | [`Caller.control_preparation_soundness`](Theorems.lean) |
| Two preparations share their actual cut states and the complete intervening machine/worker history; neither control is supplied. | [`Caller.control_preparation_window_soundness`](Theorems.lean) |
| Two native windows and their gap execute continuously from one initialization with retained tokens and clocks. | [`Caller.mixed_window_chain_soundness`](Theorems.lean) |
| An arbitrary ordered finite list of native windows and gaps shares that continuous execution. | [`Caller.mixed_window_sequence_soundness`](Theorems.lean) |
| Complete prepared G/Keccak and extended-BLAKE references reach the selected actual cut states; masks are derived. | [`Caller.prepared_hash_window_soundness` and `Caller.prepared_round_window_soundness`](Theorems.lean) |
| Two complete prepared G/Keccak references use the same continuously executed states across the intervening preparation and other effects. | [`Caller.prepared_hash_chain_soundness`](Theorems.lean) |
| A nonempty ordered list of complete prepared G/Keccak references binds every span to that same continuous execution. | [`Caller.prepared_hash_sequence_soundness`](Theorems.lean) |
| Public LUI preparation and raw matching derive exclusive masks inside each selected extended-BLAKE caller region, retaining earlier workers. | [`Caller.prepared_round_region_masks_soundness`](Theorems.lean) |
| Ordered complete G/extended-BLAKE/Keccak lists share one execution when prepared controller regions cover every extended-round worker. | [`Caller.prepared_protocol_sequence_soundness`](Theorems.lean) |
| Public caller regions derive each selected span's worker family/count before all three references compose continuously. | [`Caller.program_prepared_protocol_sequence_soundness`](Theorems.lean) |
| Modular selected span/controller regions derive shape before the same continuous complete-reference composition, retaining explicit global round coverage. | [`Caller.wrapped_program_prepared_protocol_sequence_soundness`](Theorems.lean) |
| Original current-state caller fetch, selected worker observations and PC retirement meet at the same boundaries. | [`Caller.caller_cycles_soundness`](Theorems.lean) |

Field/inverse, public boot/configuration/program/domain, modeled tables and logical
matching remain explicit. Window claims additionally retain cut alignment/location,
duration, mode/count and prefix ABI conditions. No intermediate states or scheduling
answers are supplied. Caller-cycle observations still admit the checked bigint
invalid controls, so they are not full custom-CSR execution.

Start with [Theorems](Theorems.lean) and choose the exact public claim.
[Execution](Execution.lean), [CustomExecution](CustomExecution.lean) and
[MixedExecution](MixedExecution.lean) distinguish ordinary instructions,
pinned TRIADD/XORROT forms and their composed registry.
[Shared inputs](../../Helpers/UnifiedReduced/README.md) supply public state,
program/domain, modeled tables, matching and profile conditions.

Ordinary/custom mixed retirement derives current-state fetch, reads, selectors
and terminal PC/cells. Delegation callers are outside that instruction registry.

[CallerCycles](CallerCycles.lean) binds full-family fetch, actual worker observations
and Sail PC retirement at shared cycle boundaries. It is not a complete custom-CSR
ABI theorem: the issued bigint invalid-control fixtures still satisfy those observations.

[MixedWindows](MixedWindows.lean) and [WindowProjection](WindowProjection.lean)
expose actual cut states. [JointHashWindows](JointHashWindows.lean),
[PreparedHashWindows](PreparedHashWindows.lean) and
[PreparedRoundWindows](PreparedRoundWindows.lean) bind complete selected references
at those boundaries. Prepared G/Keccak spans admit earlier workers, including
unissued effects; only the last preparation cycle is worker-free. The original
first-span extended-BLAKE entry retains its empty prefix. Public preparation/count/duration and these restrictions
remain explicit; cuts do not reset clocks or supply intermediate states.
The public ordinary registry may contain different literal writes or arbitrary
ADD/SUB/ADDI/LUI/AUIPC operands along a straight path with callers. Each preparation
cut derives its final literal and register from
that public address. Prepared G/Keccak windows inherit this scope, allowing explicit
mode changes or resets between spans; completion alone does not restart a protocol.
G/Keccak require their own family only inside the selected span. Bigint, G and
Keccak workers outside it remain in joint history; this scope excludes extended
round workers because their masks need separate transport. It adds no bigint
control-validity condition. [Control preparation](ControlPreparation.lean) also
connects two prepared controls through one intervening native window.
[`WindowChain.Realizes`](MixedWindows.lean) names the retained tokens, actual states
and complete prefix/span/gap transfers. The second span starts from the first
span's actual finish after executing the gap. [Prepared hash chains](PreparedHashWindows.lean)
bind both complete references to those same states; neither gap effects nor clocks
are reset. Empty and nonempty gaps, fabricated gap states, and an unissued prefix
effect are checked in [native chain regressions](../../../../Tests/ControlPreparation.lean)
and [the zero-clock regression](../../../../Tests/DelegationZeroInvocation.lean).
These are memory/reference claims; instruction retirement remains separate.
The [arithmetic-prefix regression](../../../../Tests/ControlPreparation.lean)
derives actual ADD→ADDI-reset states 65537→131074→0 in that same continuous history,
despite reversed native rows. The preparation read uses the actual clock-six ADD
token, and the reset retains clock ten. Fabricated reads fail joint matching.
The [`SequentialProgram`](../../Helpers/UnifiedReduced/ControlPreparation.lean)
profile also admits LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT before
the final literal. Original public decoding and native constraints derive the
PC-increment selectors; jumps, branches and wraparound comparisons remain outside
this profile. The same fixture checks TRIADD→ADDI with actual states
65537→196611→0 and rejection of a fabricated reset read. Prefix retirement and
discarded-load semantics remain separate from preparation/memory transport.
The separate [`WrappedSequentialProgram`](../../Helpers/UnifiedReduced/ControlPreparation.lean)
adds the four original comparisons and public code alignment, with modeled setup
and `4194304 ≤ p` explicit. Native constraints and matching derive modular RV32
program addresses. The [comparison-wrap regression](../../../../Tests/UnifiedComparison.lean)
checks SLTIU at `0xfffffffc` followed by ADDI at zero, actual x12 = 65537→1→0
in one history, retained clocks six/ten and rejection of a fabricated read or
wrong literal. Prepared entries using control preparation inherit this variant;
selected caller/controller region shape and global round-CSR occurrence coverage
now also use modular addresses. Jumps, branches and nonliteral preparation remain
open, as does whole caller retirement.

[`WrappedProgramCallerRegion`](../../Helpers/UnifiedReduced/WindowSchedule.lean)
states the public ordinary-exclusion/full-CSR-family policy at every clock in the
selected interval. Native matching derives counts and unique request slots without
PC injectivity or no-wrap assumptions. The corresponding
[`WrappedProgramPreparedProtocolInputs`](PreparedRoundWindows.lean) derives local
controller shape before reusing the existing raw-mask and reference proofs.
Public cuts, preparation, reference duration and global extended-round worker
coverage remain explicit. The unissued-round mask/coverage boundary is unchanged;
unissued G effects and both bigint-control gaps remain admitted. The original
linear entries and their global issued-round coverage/mask results remain available.

[`WindowSequence.Realizes`](MixedWindows.lean) extends this connection to an
arbitrary finite list. Its initial cut follows the actual prefix; every segment
executes its gap from the preceding actual finish, then its complete window.
[`WindowsOrdered`](MixedWindows.lean) makes cut order/alignment explicit and permits
empty windows and gaps. [`PreparedHashSequenceResult`](PreparedHashWindows.lean)
binds each complete G/Keccak reference, request permutation and caller count to
the corresponding segment. Every span keeps its own public preparation,
mode/count/duration and nonround worker scope; protocol shape is not inferred from
general acceptance. Three-window regressions retain actual controls across empty
and nonempty gaps, reject overlap/unaligned cuts, and preserve the unissued prefix.

The broader [prepared protocol inputs](PreparedRoundWindows.lean) allow extended
BLAKE alongside G, Keccak and bigint in the same history.
[`RoundRegionInputs`](PreparedRoundWindows.lean) binds each LUI restart to a
homogeneous caller region with at most ten positions. Raw prefix/window matching
derives its masks before any mask-dependent Sail transport; its control token
keeps the actual preparation timestamp. Earlier workers and earlier controller
regions stay in the prefix. [`PreparedProtocolInputs`](PreparedRoundWindows.lean)
requires these regions to cover every extended-round worker. This explicit
coverage replaces the global empty-prefix/family/ten-row restrictions in this
entry point; it does not derive unrestricted protocol validity from acceptance.
[`PreparedProtocolWindowInputs`](PreparedRoundWindows.lean) retains each selected
complete span's preparation, family, count and duration. The sequence theorem binds
all three complete references to their actual segment states without resetting
clocks. Completion alone is still not a controller restart. The regional seed,
wrong-flag/two-bit and retained-unissued-effect regressions are linked above.

[`ProgramProtocolWindowInputs`](PreparedRoundWindows.lean) replaces those selected
worker family/count premises with a public
[`ProgramCallerRegion`](../../Helpers/UnifiedReduced/WindowSchedule.lean).
The ordinary registry uses `SequentialProgram`; public PC/clock intervals exclude
ordinary entries and identify the CSR family. Accepted matching derives the actual
caller region and worker count from the public reference duration. The stronger
sequence theorem reaches the same complete references and actual segment states.
[`ProgramPreparedProtocolInputs`](PreparedRoundWindows.lean) now also derives the
local extended-round controller shape. Its
[`ProgramRoundRegionInputs`](PreparedRoundWindows.lean) supplies public CSR regions,
LUI preparation and at most forty ticks between ordered aligned cuts. Matching
derives local worker family/count, the ten-position bound and exact duration;
the existing regional proof derives masks before transport and reference composition.
[`ProtocolContextInputs`](PreparedRoundWindows.lean) shares public code/memory/table
conditions with the legacy regional interface. Global extended-round coverage
remains explicit, since live matching does not exclude surplus zero-clock workers.
Empty regions retain actual clock-six preparation tokens; wrong flags/family,
oversized/reversed/unaligned cuts and simultaneous round bits are rejected in
[preparation regressions](../../../../Tests/ControlPreparation.lean) and
[unified regressions](../../../../Tests/UnifiedDelegation.lean).
The stronger context retains the actual unissued G-prefix effect in
[zero-clock regressions](../../../../Tests/DelegationZeroInvocation.lean).
Public preparation/mode/duration and aligned ordered cuts remain explicit;
global controller coverage and unrestricted protocol validity remain open. COPY→ADDI and both
invalid bigint control fixtures check the schedule connection; wrong CSR family
and inclusion of ordinary code are rejected in
[the unified regressions](../../../../Tests/UnifiedDelegation.lean).

[`ProgramRoundCallerCoverage`](PreparedRoundWindows.lean) places each public decoded
extended-round CSR in a prepared region. Native PC/clock matching locates its actual
caller, and full CSR/request matching identifies the actual worker in that region.
[`RoundWorkerCoverage`](PreparedRoundWindows.lean) states the checked equivalence:
an extended-round worker belongs to a region exactly when its invocation is live.
Public LUI preparation and raw regional matching then derive exclusive masks for
every issued round worker. This local proof uses `ProtocolContextInputs`, with
full worker coverage reserved for global mask-dependent transport. The
[two-bit regression](../../../../Tests/ControlPreparation.lean) rejects two selected
round bits from these public inputs and a live target, without assumed masks or
whole-pool coverage.
The coverage equivalence assumes neither whole-pool worker coverage nor nonzero
invocations. Full coverage
is consequently equivalent to absence of zero-clock extended-round workers in this
public sequential/controller profile; their general exclusion or mask behavior
still needs a binding before global transport. Public-code regressions require a
nonempty covering interval for a decoded round CSR and preserve empty LUI-prepared
cuts. The actual unissued G worker and its prefix update remain admitted.

[`WrappedProgramRoundCallerCoverage`](PreparedRoundWindows.lean) extends coverage
to the aligned sequential/comparison registry. It covers every aligned clock
between the supplied native endpoints at which a public round CSR equals the
modular program address. Accepted constraints and state matching derive each
caller's clock interval; modular PC matching locates the actual occurrence and
request matching identifies its worker. This avoids a PC-injectivity or no-wrap
premise. The modular coverage, issued-mask and full-coverage boundary theorems
above retain the same unissued-round limitation. Regressions reject covering only
one of two occurrences 2^32 ticks apart in a public code-policy fixture (without
an accepted-trace claim), admit an empty prepared cut, reject two issued round
bits without whole-pool coverage, and retain the actual zero-clock G worker.

Keep surplus zero-clock prefix effects, worker ROM-shadow transport,
broader preparation/protocol binding, full mixed caller retirement and inactive padding as separate
outstanding obligations. [Status](../../../../VERIFICATION_STATUS.md) records the scope.
