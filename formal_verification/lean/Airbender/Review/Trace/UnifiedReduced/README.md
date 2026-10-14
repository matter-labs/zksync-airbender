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
| Actual joint cut states and projected worker boundaries retain native timestamps. | [`Caller.mixed_window_soundness` and `Caller.mixed_window_projection_soundness`](Theorems.lean) |
| Uniform or successive public ADDI-from-x0/LUI preparation yields actual controls; native PC/clock matching derives the instruction at each cut. | [`Caller.control_preparation_soundness`](Theorems.lean) |
| Two preparations share their actual cut states and the complete intervening machine/worker history; neither control is supplied. | [`Caller.control_preparation_window_soundness`](Theorems.lean) |
| Two native windows and their gap execute continuously from one initialization with retained tokens and clocks. | [`Caller.mixed_window_chain_soundness`](Theorems.lean) |
| An arbitrary ordered finite list of native windows and gaps shares that continuous execution. | [`Caller.mixed_window_sequence_soundness`](Theorems.lean) |
| Complete prepared G/Keccak and extended-BLAKE references reach the selected actual cut states; masks are derived. | [`Caller.prepared_hash_window_soundness` and `Caller.prepared_round_window_soundness`](Theorems.lean) |
| Two complete prepared G/Keccak references use the same continuously executed states across the intervening preparation and other effects. | [`Caller.prepared_hash_chain_soundness`](Theorems.lean) |
| A nonempty ordered list of complete prepared G/Keccak references binds every span to that same continuous execution. | [`Caller.prepared_hash_sequence_soundness`](Theorems.lean) |
| Public LUI preparation and raw matching derive exclusive masks inside each selected extended-BLAKE caller region, retaining earlier workers. | [`Caller.prepared_round_region_masks_soundness`](Theorems.lean) |
| Ordered complete G/extended-BLAKE/Keccak lists share one execution when prepared controller regions cover every extended-round worker. | [`Caller.prepared_protocol_sequence_soundness`](Theorems.lean) |
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
The public ordinary registry may contain different literal writes along a straight
path with callers. Each preparation cut derives its own literal and register from
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

Keep surplus zero-clock prefix effects, worker ROM-shadow transport,
broader preparation/protocol binding, full mixed caller retirement and inactive padding as separate
outstanding obligations. [Status](../../../../VERIFICATION_STATUS.md) records the scope.
