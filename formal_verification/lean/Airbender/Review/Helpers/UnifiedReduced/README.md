# Unified execution inputs and preparation

These helpers state the public configuration, program/domain, decoding and
complete-protocol scope consumed by the unified trace theorems. They do not
supply desired reads, arithmetic results, valid native controls or successful
execution. Accepted constraints and one initialized history derive those facts.

## Checked results

[Execution inputs](ExecutionInputs.lean) connect the original program and public
Sail state to unified ordinary/custom retirement. [Native ROM views](NativeROM.lean)
keep public instruction bytes distinct from native zero ROM shadows.
[Retirement profiles](RetirementProfile.lean) retain configuration, readonly code,
tracked data RAM and the unchanged-Sail discarded-load restriction.

[Control preparation](ControlPreparation.lean) and
[PC-relative preparation](PCRelativePreparation.lean) bind original public
instruction forms to actual values/timestamps through native decoding and memory.
[Register dataflow](RegisterDataflow.lean) composes computed literal/arithmetic
preparation and native caller effects; [register chains](RegisterChains.lean)
retain actual writes and read refreshes across admitted gaps. These are value
transport interfaces; whole prefix retirement is a separate result.

The existing `WrappedSequentialProgram` registry includes the supported
straight-line ordinary/custom operations and comparisons, excluding branches,
JAL and JALR. The [full execution theorem](../../Trace/UnifiedReduced/FullExecution.lean)
uses that registry and the complete selected-reference protocol inputs.
[Actual-path execution](../../Trace/UnifiedReduced/PathExecution.lean) and
[complete spans](../../Trace/UnifiedReduced/PathSpanExecution.lean) use actual
instruction occurrences to compose branches, jumps and loops with complete
workers. Their general proofs, the accepted two-COPY loop and the accepted
native [G-loop application](../../../../Tests/PathGLoop.lean) pass focused kernel
checks. The latter retains all three full runs, groups the baseline and scratch
SW7 complete 56-call protocols, and refutes actual endpoint [`WordMapping`](../../Trace/Workers/Blake2G/WorkVector.lean) and
[`PathSpanAlgorithmAt`](../../Trace/UnifiedReduced/Paths/SpanProjection.lean) for the protected-message SW7 variant. Its 55 repeated loop
calls and last index 55/controller 183 use public occurrence preparation. Complete
mitigation assurance and full independent kernel replay remain pending.

## Conditions that remain public

Initial state/program/configuration, aligned tracked domain, modeled tables,
exact logical matching and selected protocol shape remain explicit. Native
initialization derives zero seeds, geometry and register coverage; register
values/teardown and the intended public state are separate inputs. Sampled RAM
product equality does not establish deterministic token-multiset equality.

Worker-only clockRoom and invocationHigh remain explicit in their own interfaces.
Integrated native clocks and initialized caller accounting derive participation
and their corresponding bounds. Complete references retain public modes, window
coverage and applicable controller extents. F02 bigint commands and F04 worker
RAM ports remain separate enforcement findings. No standard boot-ROM-data-copy
claim follows from readonly code and tracked RAM above the ROM limit.

Pure programEntryWith decoding and stateful programEntryRunWith decoding have
different contracts: the latter runs Sail on public state and may read misa for
REV8. Consolidation must preserve that distinction.

## Review route

Read the chosen [trace claim](../../Trace/UnifiedReduced/README.md) and its input
record first, then follow the preparation/dataflow helper needed for that claim.
[History](HISTORY.md) retains the earlier construction stages and regression
narratives. Supporting calculation proofs stay in Proofs; important composed
claims and visible public conditions stay in Review.

The [TRIADD preparation fixture](../../../../Tests/ControlPreparationBase.lean)
checks `triadd_prefix_and_preparation_share_history` and rejects a fabricated
preparation read in that same history.
