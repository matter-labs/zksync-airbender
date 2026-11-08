# Unified execution review

This directory states execution claims for the unified artifact: ordinary and
selected custom instruction retirement, caller-cycle observations, and complete
reference effects on selected native-clock windows. The claims share actual
history-derived states but use different registries and input contracts; full
mixed execution with delegation callers remains a separate obligation.

## Checked results

| Result from accepted history and stated public inputs | Direct theorem in Theorems |
| --- | --- |
| Original standard instructions retire and reach native terminal PC/cells, using public ROM bytes. | [`rv_execution_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Standard instructions plus TRIADD/XORROT retire together; delegation callers are outside the registry. | [Mixed.execution_soundness](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Machine and worker reads/writes, bounds and references share one actual initialized history. | [`Caller.rv_mixed_memory_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Exact caller regions, counts and slots follow from state/request matching and public cuts/duration. | [`Caller.rv_window_schedule_soundness` and `Caller.rv_request_window_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Public sequential code identifies caller regions; native matching derives selected worker family, counts and slots. | [`Caller.rv_program_window_schedule_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Actual joint cut states and projected worker boundaries retain native timestamps. | [`Caller.rv_mixed_window_soundness` and `Caller.rv_mixed_window_projection_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Public ADDI-from-x0/LUI preparation yields actual controls after literal or sequential ordinary/custom prefixes; native PC/clock matching derives each preparation address. | [`Caller.rv_control_preparation_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Two preparations share their actual cut states and the complete intervening machine/worker history; neither control is supplied. | [`Caller.rv_control_preparation_window_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Two native windows and their gap execute continuously from one initialization with retained tokens and clocks. | [`Caller.rv_mixed_window_chain_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| An arbitrary ordered finite list of native windows and gaps shares that continuous execution. | [`Caller.rv_mixed_window_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Complete prepared G/Keccak and extended-BLAKE references reach the selected actual cut states; masks are derived. | [`Caller.rv_prepared_hash_window_soundness` and `Caller.rv_prepared_round_window_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Two complete prepared G/Keccak references use the same continuously executed states across the intervening preparation and other effects. | [`Caller.rv_prepared_hash_chain_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| A nonempty ordered list of complete prepared G/Keccak references binds every span to that same continuous execution. | [`Caller.rv_prepared_hash_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Public LUI preparation and raw matching derive exclusive masks inside each selected extended-BLAKE caller region, retaining earlier workers. | [`Caller.rv_prepared_round_region_masks_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Ordered complete G/extended-BLAKE/Keccak lists share one execution when prepared controller regions cover every extended-round worker. | [`Caller.rv_prepared_protocol_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Public caller regions derive each selected span's worker family/count before all three references compose continuously. | [`Caller.rv_program_prepared_protocol_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Original current-state caller fetch, selected worker observations and PC retirement meet at the same boundaries. | [`Caller.rv_caller_cycles_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |

Field/inverse, public boot/configuration/program/domain, modeled tables and logical
matching remain explicit. Window claims additionally retain cut alignment/location,
duration, mode/count and prefix ABI conditions. No intermediate states or scheduling
answers are supplied. Caller-cycle observations still admit the checked bigint
invalid controls, so they are not full custom-CSR execution.

Start with [Theorems](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) and choose the exact public claim.
Execution, CustomExecution and
MixedExecution distinguish ordinary instructions,
pinned TRIADD/XORROT forms and their composed registry.
[Shared inputs](../../Helpers/UnifiedReduced/README.md) supply public state,
program/domain, modeled tables, matching and profile conditions.

Ordinary/custom mixed retirement derives current-state fetch, reads, selectors
and terminal PC/cells. Delegation callers are outside that instruction registry.

CallerCycles binds full-family fetch, actual worker observations
and Sail PC retirement at shared cycle boundaries. It is not a complete custom-CSR
ABI theorem: the issued bigint invalid-control fixtures still satisfy those observations.

[MixedWindows](MixedWindows.lean) and WindowProjection
expose actual cut states. JointHashWindows,
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
control-validity condition. Control preparation also
connects two prepared controls through one intervening native window.
[WindowChain.Realizes](MixedWindows.lean) names the retained tokens, actual states
and complete prefix/span/gap transfers. The second span starts from the first
span's actual finish after executing the gap. [Prepared hash chains](PreparedHashWindows.lean)
bind both complete references to those same states; neither gap effects nor clocks
are reset. Empty and nonempty gaps, fabricated gap states, and an unissued prefix
effect are checked in [native chain regressions](../../../../test/Tests/ControlPreparation.lean)
(the zero-clock worker those regressions used is now rejected by the circuit:
[zero-clock regression](../../../../test/Tests/DelegationZeroInvocation.lean)).
These are memory/reference claims; instruction retirement remains separate.
The [arithmetic-prefix regression](../../../../test/Tests/ControlPreparation.lean)
derives actual ADD→ADDI-reset states 65537→131074→0 in that same continuous history,
despite reversed native rows. The preparation read uses the actual clock-six ADD
token, and the reset retains clock ten. Fabricated reads fail joint matching.
The [`RVSequentialProgram`](../../Helpers/UnifiedReduced/ControlPreparation.lean)
profile also admits LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT before
the final literal. Original public decoding and native constraints derive the
PC-increment selectors; jumps, branches and wraparound comparisons remain outside
this profile. The same fixture checks TRIADD→ADDI with actual states
65537→196611→0 and rejection of a fabricated reset read. Prefix retirement and
discarded-load semantics remain separate from preparation/memory transport.

[WindowSequence.Realizes](MixedWindows.lean) extends this connection to an
arbitrary finite list. Its initial cut follows the actual prefix; every segment
executes its gap from the preceding actual finish, then its complete window.
[`WindowsOrdered`](MixedWindows.lean) makes cut order/alignment explicit and permits
empty windows and gaps. [`RVPreparedHashSequenceResult`](PreparedHashWindows.lean)
binds each complete G/Keccak reference, request permutation and caller count to
the corresponding segment. Every span keeps its own public preparation,
mode/count/duration and nonround worker scope; protocol shape is not inferred from
general acceptance. Three-window regressions retain actual controls across empty
and nonempty gaps, reject overlap/unaligned cuts, and preserve the unissued prefix.

The broader [prepared protocol inputs](PreparedRoundWindows.lean) allow extended
BLAKE alongside G, Keccak and bigint in the same history.
[`RVRoundRegionInputs`](PreparedRoundWindows.lean) binds each LUI restart to a
homogeneous caller region with at most ten positions. Raw prefix/window matching
derives its masks before any mask-dependent Sail transport; its control token
keeps the actual preparation timestamp. Earlier workers and earlier controller
regions stay in the prefix. [`RVPreparedProtocolInputs`](PreparedRoundWindows.lean)
requires these regions to cover every extended-round worker. This explicit
coverage replaces the global empty-prefix/family/ten-row restrictions in this
entry point; it does not derive unrestricted protocol validity from acceptance.
[`RVPreparedProtocolWindowInputs`](PreparedRoundWindows.lean) retains each selected
complete span's preparation, family, count and duration. The sequence theorem binds
all three complete references to their actual segment states without resetting
clocks. Completion alone is still not a controller restart. The regional seed,
wrong-flag/two-bit and retained-unissued-effect regressions are linked above.

[`RVProgramProtocolWindowInputs`](PreparedRoundWindows.lean) replaces those selected
worker family/count premises with a public
`RVProgramCallerRegion`.
The ordinary registry uses `RVSequentialProgram`; public PC/clock intervals exclude
ordinary entries and identify the CSR family. Accepted matching derives the actual
caller region and worker count from the public reference duration. The stronger
sequence theorem reaches the same complete references and actual segment states.
It retains public preparation/mode/duration, aligned ordered cuts and the shared
extended-round controller-region coverage. Controller coverage and unrestricted
protocol validity are not conclusions of this new entry. COPY→ADDI and both
invalid bigint control fixtures check the schedule connection; wrong CSR family
and inclusion of ordinary code are rejected in
[the unified regressions](../../../../test/Tests/UnifiedDelegation.lean).

Keep surplus zero-clock prefix effects, worker ROM-shadow transport,
broader preparation/protocol binding, full mixed caller retirement and inactive padding as separate
outstanding obligations. [Status](../../../../../docs/VERIFICATION_STATUS.md) records the scope.
