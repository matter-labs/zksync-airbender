# Unified reduced-machine execution

This directory connects accepted unified rows, all four worker families and one
initialized memory history to reference execution and native terminal PC/cells.
Original standard instructions use the pinned Sail clauses. TRIADD, XORROT and
custom CSR effects use the pinned project references.

[StreamCalls](StreamCalls.lean) defines a candidate unified machine relation
combining ordinary/modular steps, external `0x7C0` reads and complete caller
retirement. Its [first inclusion proofs](../../../Proofs/UnifiedReduced/StreamCalls.lean)
establish disjoint decoder registries and lift modular and caller steps. No
native whole-execution soundness theorem for this combined relation is proved yet.

## Checked results

[Ordinary/custom retirement](Theorems.lean) supports the selected standard
instructions, TRIADD, XORROT and the separately composed
[modular operations](ModularExecution.lean). Ordinary branches, JAL and JALR have
native trace proofs.

[Mixed cycles](MixedCycles.lean) places ordinary retirement, caller observations,
worker states and the actual raw PC/clock path in the same initialized history.
Its observation certificate alone does not assert successful full custom calls.

[Full execution](FullExecution.lean) composes complete bigint, BLAKE2 G,
extended-round and special5 Keccak references with the supported straight-line ordinary
registry. It starts at the original public state and reaches native terminal
PC/cells. The F02 command contract remains explicit. Current native BabyBear
constraints and caller accounting derive participation; no external occurrence
ledger is supplied.

[Supported-use execution](SupportedUseExecution.lean) replaces bigint/hash
witness premises with the public
[ValidDelegationUse](DelegationUse.lean) contract. It states
the registered wrapper shapes, safe entry and runtime controls/pointers over
independent reference prefixes. The native bridge cuts before each instruction
and inducts on its clock; an earlier accepted prefix supplies the reference state
whose arguments determine the next worker's inputs. Exact matching and the
public initialization/RAM/configuration/setup profile remain explicit.
The covered wrappers are bigint, G and extended round. G separation stays a
program obligation; blessed split Keccak is a required, open part of the full
unsigned target (F12).

The lower-level [native actual-path execution](NativePathExecution.lean) composes branches, JAL,
JALR and repeated-PC loops with complete calls from all four worker families.
The [F11 hash witness contracts](../../../../FINDINGS.md#f11--hash-witness-contracts-remain-unenforced),
implemented by [HashCommands](../../Helpers/UnifiedReduced/NativeMemory.lean),
assume supported private controller reads and G base separation. The
[individual conditions](../../Helpers/Context/ExternalBoundary/HashABI.lean)
are not proved from the restored native circuits; they contain no outputs or
desired execution. Per-call validity does not enforce the VM's zero bundle entry.
The zero round low limb agrees with the blessed callers' mask rule; arbitrary
VM calls have a wider domain. Controllers may be loaded or computed through ordinary
instructions. No occurrence plan is supplied. The conclusion realizes
the native terminal PC and every tracked cell. Public program/initialized memory,
configuration/retirement and the separate bigint command contract remain explicit.
The older [prepared actual-path interface](PathExecution.lean) retains its
trace-dependent instruction/caller plan for compatibility.
The repeated-PC G-loop fixture exercises these lower-level conditional APIs;
its loop around one CSR is not a blessed contiguous wrapper or a supported-use
example. The supported-use theorem proves instruction-prefix execution; complete
algorithm claims still require the span coverage and gap conditions below.

[Complete actual-path spans](PathSpanExecution.lean) also derives the full worker
partition/count and complete algorithms in one history under its per-trace
occurrence plan and complete protocol coverage. Each span uses readonly
gaps or computed stores disjoint from its protected blocks. Other ordinary
writes retain their whole-execution meaning without a grouped algorithm claim.

[Hash segmentation](Segmentation.lean) derives a disjoint exact partition of
issued hash workers into complete selected references under the existing public
prepared-protocol scope. Public protocol shape is not inferred from arbitrary
acceptance.

## Inputs and conclusions

Review the [retirement profile](../../Helpers/UnifiedReduced/RetirementProfile.lean),
[control preparation](../../Helpers/UnifiedReduced/ControlPreparation.lean) and
[computed protocol inputs](ComputedRoundRegions.lean) beside the full conclusion.
Public code, configuration, initial state/domain, modeled tables, exact matching,
selected modes and complete protocol coverage remain inputs. Reads, operands,
actual worker effects, native clock order and retirement are derived.

Preparation transports values through native memory. Successful execution of a
whole prefix is a separate conclusion; it is not smuggled into a preparation
assumption. Pure decoding and stateful program decoding remain distinct because
stateful decoding may read public configuration such as misa.

## Current restrictions

The older straight-line full-CSR entrypoint retains WrappedSequentialProgram;
the actual-path entrypoints cover branches, jumps and loops. Both retain the
code/profile restriction that tracked data RAM lies at or above the ROM limit.
The concrete accepted two-COPY loop application passes focused kernel checks,
including terminal PC/cells. The accepted native
[G-loop application](../../../../Tests/PathGLoop.lean) also passes focused kernel
checks: `Tests.PathGLoop.complete_regression` retains all three full executions
and terminal PC 160/cells, 55 repeated loop calls and the final index 55/controller 183.
The baseline and scratch SW7 variants group the complete 56-call G protocol;
the protected-message SW7 variant refutes actual endpoint [`WordMapping`](../Workers/Blake2G/WorkVector.lean) and
[`PathSpanAlgorithmAt`](Paths/SpanProjection.lean) while retaining its full execution. The complete mitigation
assurance sweep and full independent kernel replay remain pending. Standard
boot-ROM-data copying remains outside the claim.

The [native mixed-ROM composition](NativeMixedROM.lean) preserves public program
bytes, native ROM shadows and actual RAM-worker transfers. ROM-pointer invocations and invalid bigint controls remain excluded by
supported delegation use; lower-level counterexamples are retained under F04/F02. Canonical endpoint and padding closure come from their explicit
external logical boundaries, with cryptographic and Rust enforcement separate.

## Review route

Start with [FullExecution](FullExecution.lean) and its input records, then follow
[caller cycles](CallerCycles.lean), [complete bigint calls](BigintCalls.lean),
[computed hash windows](ComputedHashWindows.lean) and
[prepared round windows](PreparedRoundWindows.lean) as required by the chosen scope.
[Initialization adapters](../Initialization.lean) derive native seed/domain
properties for ordinary pooled/unified execution from actual standalone/inline
boundaries. The delegation and other extended registries retain their own seed
premises; public Sail/profile and exact matching remain explicit.

Worker-only clockRoom and invocationHigh are separate from integrated caller
bounds. Weaker zero-clock and observation interfaces retain their documented
local scopes. The [historical record](../../../../REVIEW_TRACE_HISTORY.md) preserves dated fixtures and
construction stages; it is not the current reading path.
