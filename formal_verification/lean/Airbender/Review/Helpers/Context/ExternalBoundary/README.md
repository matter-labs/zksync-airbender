# Temporary contracts for open findings

These contracts support conditional proofs. Their individual
[finding statuses](../../../../../FINDINGS.md#linear-and-open-pr-review--15-october-2026)
distinguish open defects from validated source fixes with unproved formal bindings.
The generic contracts remain explicit at their conditional entries. Current
native BabyBear constraints and initialized caller accounting now derive the
Requests ledger; full mixed execution uses that derivation. The other contracts
retain the implementation and formal-binding boundaries listed below.

| Contract | Conditional consequence | Finding and missing enforcement |
| --- | --- | --- |
| [Hash controllers and G bases](HashABI.lean) | Together with native arithmetic and initialized history, `HashCommands` supports the conditional actual-path execution theorem. | Temporary input restrictions: G supported controls and distinct block bases; extended-round canonical controls and supported round; Keccak control membership in the existing protocol. Native enforcement remains open after removal of the circuit patches. The round zero low limb is a proof-profile restriction, not an asserted VM requirement. No output, reference execution, occurrence plan or complete protocol is assumed. |
| [Initialization](Initialization.lean) | Typed window geometry and distinct selected indices give distinct aligned physical cells, including all GPRs. | AIH-334's EVM validation is implemented and tested; formal correspondence remains external. Geometry comes from the target layout; no copied fixed ceiling, contiguous-window requirement or assumed public memory values. |
| [Decoder](Decoder.lean) | Committed real rows plus unreachable filler and exact active query binding imply the existing logical public decoder membership. | AIH-336 / F09: source tail/cache correction and CPU regressions now exist; accelerated runtime/proof replay validation and formal extraction/authentication/query binding remain open. The contract itself is unchanged. |
| [Requests](Requests.lean) | A full occurrence ledger gives every worker a caller at its native slot. | Current BabyBear timestamp constraints exclude active zero clocks; [native accounting](../../../../Proofs/ExternalBoundary/NativeRequests.lean) derives the ledger from accepted constraints and initialized caller binding. The generic contract remains available for weaker profiles. No clock-positivity or worker-result premise is added. |
| [Bigint control](BigintABI.lean) | Full x12 binding to one opcode plus carry now supports [complete bigint call retirement](../../../Trace/UnifiedReduced/BigintCalls.lean), with pointers/operands/frame derived from accepted initialized history. | F02: native acceptance admits controls 0/65537. This is temporary control validation, not an implementation fix; it supplies no pointers, operands, results or desired execution. Carry uses bit six; COPY uses bit seven. |
| [Worker RAM](WorkerRAM.lean) | [Whole mixed-memory composition](../../../Trace/UnifiedReduced/NativeMixedROM.lean) now derives physical boot initialization and one public-byte ordinary/caller/worker history with terminal cells. | F04: accepted ROM-shadow COPY remains a discrepancy. The address-only restriction supplies neither reads nor writes; arbitrary native acceptance has not established it. |

[Public conditional results](../../../Trace/ExternalBoundaries.lean) reuse
the [proof implementations](../../../../Proofs/ExternalBoundary/Initialization.lean).
They expose each conditional premise directly. Terminal-PC, inactive-row,
invalid-control and ROM-shadow fixtures retain their scopes. The
[zero-clock fixture](../../../../../Tests/DelegationZeroInvocation.lean) retains
its raw arithmetic, token cancellation and padding behavior, and now proves
rejection by the current native timestamp constraints. Passing a temporary contract is not a finding-closure
criterion: inspect and validate the actual implementation fix or independent
global enforcement before changing the finding's status.

Canonical [verifier-PC](../VerifierBoundary/README.md) and
[padding-mask](../PaddingBoundary/README.md) bindings are intended external
interfaces with inspected source mechanisms; their Rust/argument refinement
remains external. Public machine configuration and supported protocol profiles
are explicit scope choices. The [trust guide](../../../../../TRUST_AND_REVIEW.md)
keeps those categories distinct from the missing checks above. Transcript
freshness, recursive-output binding, cryptographic soundness and compilation
fidelity are not supplied by any of these five contracts.
