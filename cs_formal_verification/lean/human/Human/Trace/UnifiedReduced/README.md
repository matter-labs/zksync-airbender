# Unified execution review

This directory states execution claims for the unified artifact: ordinary and
selected custom instruction retirement, caller-cycle observations, and complete
reference effects on selected native-clock windows. The claims share actual
history-derived `RV.State`s but use different registries and input contracts; full
mixed execution with delegation callers remains a separate obligation.

## Checked results

Every unified claim also has a `…SatisfiableClaim` beside it: booted traces, caller traces with LUI/ADDI preparation
rows and complete hash spans in [Satisfiable/UnifiedCallers](../../../../slop/Slop/Final/Trace/Satisfiable/UnifiedCallers.lean).

The ordinary claim is [RVTheorems](RVTheorems.lean); the `Caller.*` claims are in
[RVCallerTheorems](RVCallerTheorems.lean). Proofs are in `slop/Slop/Final/Trace/UnifiedReduced/`.

| Result from accepted history and stated public inputs | Direct theorem |
| --- | --- |
| Standard instructions plus TRIADD/XORROT retire together as a run of `RV.run` and reach native terminal PC/cells, using public ROM bytes; delegation callers are outside the registry. | [`rv_execution_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) |
| Machine and worker reads/writes, bounds and references share one actual initialized history. | [`Caller.rv_mixed_memory_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Exact caller regions, counts and slots follow from state/request matching and public cuts/duration. | [`Caller.rv_window_schedule_soundness` and `Caller.rv_request_window_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Public sequential code identifies caller regions; native matching derives selected worker family, counts and slots. | [`Caller.rv_program_window_schedule_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Actual joint cut states and projected worker boundaries retain native timestamps. | [`Caller.rv_mixed_window_soundness` and `Caller.rv_mixed_window_projection_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Public ADDI-from-x0/LUI preparation yields actual controls after literal or sequential ordinary/custom prefixes; native PC/clock matching derives each preparation address. | [`Caller.rv_control_preparation_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Two preparations share their actual cut states and the complete intervening machine/worker history; neither control is supplied. | [`Caller.rv_control_preparation_window_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| An arbitrary ordered finite list of native windows and their gaps executes continuously from one initialization with retained tokens and clocks. | [`Caller.rv_mixed_window_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Complete prepared G/Keccak and extended-BLAKE references reach the selected actual cut states; masks are derived. | [`Caller.rv_prepared_hash_window_soundness` and `Caller.rv_prepared_round_window_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| A nonempty ordered list of complete prepared G/Keccak references uses the same continuously executed states across the intervening preparation and other effects. | [`Caller.rv_prepared_hash_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Public LUI preparation and raw matching derive exclusive masks inside each selected extended-BLAKE caller region, retaining earlier workers. | [`Caller.rv_prepared_round_region_masks_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Ordered complete G/extended-BLAKE/Keccak lists share one execution when prepared controller regions cover every extended-round worker. | [`Caller.rv_prepared_protocol_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Public caller regions derive each selected span's worker family/count before all three references compose continuously. | [`Caller.rv_program_prepared_protocol_sequence_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |
| Caller fetch (`RV.decode` to `.delegate k`), selected worker observations and the spec's PC advance meet at the same boundaries. | [`Caller.rv_caller_cycles_soundness` and `Caller.rv_prepared_round_cycles_soundness`](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean) |

Field/inverse, public boot/program/domain, modeled tables and logical
matching remain explicit. Window claims additionally retain cut alignment/location,
duration, mode/count and prefix ABI conditions. No intermediate states or scheduling
answers are supplied. The two cycle claims have no code-domain premise: the ROM image is separate from
RAM and the RV table's fetch guard places every entry in aligned ROM words. They still do not
check bigint control validity, so they are not full custom-CSR execution.

Choose the exact public claim from the table.
[Shared inputs](../../Helpers/UnifiedReduced/README.md) supply the public state (`RVBootInputs`),
program/domain, modeled tables and matching conditions. Ordinary/mixed retirement derives current-state
fetch, reads, selectors and terminal PC/cells; delegation callers are outside that instruction registry.

[RVCallerCycles](RVCallerCycles.lean) binds full-family fetch, actual worker observations
and PC retirement at shared cycle boundaries (`RVCallerCycle`).

[RVMixedWindows](RVMixedWindows.lean) and [RVWindowProjection](RVWindowProjection.lean)
expose actual cut states. [RVJointHashWindows](RVJointHashWindows.lean),
[RVPreparedHashWindows](RVPreparedHashWindows.lean) and
[RVPreparedRoundWindows](RVPreparedRoundWindows.lean) bind complete selected references
at those boundaries. Prepared G/Keccak spans admit earlier workers, including
unissued effects; only the last preparation cycle is worker-free. The original
first-span extended-BLAKE entry retains its empty prefix. Public preparation/count/duration and these restrictions
remain explicit; cuts do not reset clocks or supply intermediate states.
Completion of a protocol alone does not restart it: G/Keccak require their own family only inside the
selected span, and Bigint, G and Keccak workers outside it remain in joint history. The window-sequence
realization (`RVWindowSequence.Realizes` in
[RVMixedWindows](RVMixedWindows.lean)) names the retained tokens, actual states and complete
prefix/span/gap transfers: each segment executes its gap from the preceding actual finish, then its complete
window; `WindowsOrdered` ([MixedWindows](MixedWindows.lean)) makes cut order and alignment explicit and permits empty windows and gaps
([overlapping or unaligned sequences are rejected](../../../../test/Tests/ControlPreparation.lean)).
These are memory/reference claims; instruction retirement remains separate.

The preparation registry ([RVSequentialProgram](../../Helpers/UnifiedReduced/RVControlPreparation.lean)) admits
ADD/SUB/ADDI/LUI/AUIPC, LW/SW, bitwise/shifts, REV8 and supported TRIADD/XORROT along a straight path
with callers; jumps, branches and wraparound comparisons are outside it. Public decoding and native
constraints derive the PC-increment selectors; each preparation cut derives its final literal and register
from the public address.

The broader [prepared protocol inputs](RVPreparedRoundWindows.lean) allow extended
BLAKE alongside G, Keccak and bigint in the same history.
`RVRoundRegionInputs` binds each LUI restart to a homogeneous caller region with at most ten positions. Raw
prefix/window matching derives its masks before any mask-dependent transport; its control token keeps the actual
preparation timestamp. `RVPreparedProtocolInputs` requires these regions to cover every extended-round worker;
`RVPreparedProtocolWindowInputs` retains each selected complete span's preparation, family, count and duration.
`RVProgramProtocolWindowInputs` replaces the selected worker family/count premises with a public
`RVProgramCallerRegion` (a PC/clock interval that excludes ordinary entries and fixes the CSR family; the
ordinary registry uses `RVSequentialProgram`). Controller coverage and unrestricted protocol validity are not
conclusions of these entries.

Keep surplus zero-clock prefix effects, native unified ROM-shadow transport,
broader preparation/protocol binding, full mixed caller retirement and inactive padding as separate
outstanding obligations. [Status](../../../../../docs/VERIFICATION_STATUS.md) records the scope.
