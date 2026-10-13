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
| Public ADDI-from-x0/LUI preparation yields actual first-span controls, without desired control reads. | [`Caller.control_preparation_soundness`](Theorems.lean) |
| Complete prepared G/Keccak and extended-BLAKE references reach the selected actual cut states; masks are derived. | [`Caller.prepared_hash_window_soundness` and `Caller.prepared_round_window_soundness`](Theorems.lean) |
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
at those boundaries. Public preparation/count/duration and prefix restrictions
remain explicit; cuts do not reset clocks or supply intermediate states.

Keep surplus zero-clock prefix effects, worker ROM-shadow transport, broader
span chaining, full mixed caller retirement and inactive padding as separate
outstanding obligations. [Status](../../../../VERIFICATION_STATUS.md) records the scope.
