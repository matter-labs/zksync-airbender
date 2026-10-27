# Conditional boundary contracts

These contracts support conditional proofs. Their individual
[finding statuses](../../../../../FINDINGS.md#linear-and-open-pr-review--15-october-2026)
distinguish open defects from validated source fixes with unproved formal bindings.
The generic contracts remain explicit at their conditional entries. Current
native BabyBear constraints and initialized caller accounting now derive the
Requests ledger; full mixed execution uses that derivation. The other contracts
retain the implementation and formal-binding boundaries listed below.

For covered delegation programs, the public
[ValidDelegationUse](../../../Trace/UnifiedReduced/DelegationUse.lean) contract states wrapper shape,
safe entry and reference-prefix argument validity. The
[supported-use execution entrypoint](../../../Trace/UnifiedReduced/SupportedUseExecution.lean)
derives the bigint/hash worker conditions through exact native prefixes. The
lower-level contracts remain available for conditional worker/circuit results.
Invalid invocation reports F02/F04/F11 are outside the developers' supported-use
domain; they do not require circuit changes for these conditional claims.

| Contract | Conditional consequence | Finding and missing enforcement |
| --- | --- | --- |
| [Hash witness contracts](HashABI.lean) | Together with native arithmetic and initialized history, [HashCommands](../../UnifiedReduced/NativeMemory.lean) supports lower-level conditional actual-path execution. | [F11](../../../../../FINDINGS.md#f11--hash-witness-contracts-remain-unenforced): G controls/base separation, exclusive round masks and special5 protocol positions restrict native reads. Per-call membership alone does not ensure valid bundle entry; the public supported-use contract also states entry safety. The zero round low limb is the blessed callers' mask rule. No output, execution or complete algorithm result is supplied. |
| [Initialization](Initialization.lean) | Typed window geometry and distinct selected indices give distinct aligned physical cells, including all GPRs. | AIH-334's EVM validation is implemented and tested; formal correspondence remains external. Geometry comes from the target layout; no copied fixed ceiling, contiguous-window requirement or assumed public memory values. |
| [Decoder](Decoder.lean) | Committed real rows plus unreachable filler and exact active query binding imply the existing logical public decoder membership. | AIH-336 / F09: source tail/cache correction and CPU regressions now exist; accelerated runtime/proof replay validation and formal extraction/authentication/query binding remain open. The contract itself is unchanged. |
| [Requests](Requests.lean) | A full occurrence ledger gives every worker a caller at its native slot. | Current BabyBear timestamp constraints exclude active zero clocks; [native accounting](../../../../Proofs/ExternalBoundary/NativeRequests.lean) derives the ledger from accepted constraints and initialized caller binding. The generic contract remains available for weaker profiles. No clock-positivity or worker-result premise is added. |
| [Bigint control](BigintABI.lean) | Full x12 binding to one opcode plus carry supports [complete bigint call retirement](../../../Trace/UnifiedReduced/BigintCalls.lean), with pointers/operands/frame derived from accepted initialized history. | F02: native acceptance admits controls 0/65537, excluded by supported use. The binding supplies no pointers, operands, results or desired execution. Carry uses bit six; COPY uses bit seven. |
| [Worker RAM](WorkerRAM.lean) | [Whole mixed-memory composition](../../../Trace/UnifiedReduced/NativeMixedROM.lean) derives physical boot initialization and one public-byte ordinary/caller/worker history with terminal cells. | F04: ROM-pointer invocation is outside supported use. This lower-level address binding supplies neither reads nor writes; arbitrary native acceptance is not asserted to enforce it. |

[Public conditional results](../../../Trace/ExternalBoundaries.lean) reuse
the [proof implementations](../../../../Proofs/ExternalBoundary/Initialization.lean).
They expose each conditional premise directly. Terminal-PC, inactive-row,
invalid-control and ROM-shadow fixtures retain their scopes. The
[zero-clock fixture](../../../../../Tests/DelegationZeroInvocation.lean) retains
its raw arithmetic, token cancellation and padding behavior, and now proves
rejection by the current native timestamp constraints. Passing a conditional
contract is not an implementation fix: finding dispositions require a validated
repair, independent enforcement evidence or a justified supported-use domain.

Canonical [verifier-PC](../VerifierBoundary/README.md) and
[padding-mask](../PaddingBoundary/README.md) bindings are intended external
interfaces with inspected source mechanisms; their Rust/argument refinement
remains external. Public machine configuration and supported protocol profiles
are explicit scope choices. The [trust guide](../../../../../TRUST_AND_REVIEW.md)
keeps those categories distinct from the missing checks above. Transcript
freshness, recursive-output binding, cryptographic soundness and compilation
fidelity are not supplied by these contracts.
