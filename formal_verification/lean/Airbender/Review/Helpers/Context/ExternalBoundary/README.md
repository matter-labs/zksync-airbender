# Temporary contracts for open findings

These contracts support conditional proofs. Their individual
[finding statuses](../../../../../FINDINGS.md#linear-and-open-pr-review--15-october-2026)
distinguish open defects from validated source fixes with unproved formal bindings.
They are not proved consequences of current native/verifier acceptance,
implemented fixes, or a certificate for the full custom CSR. Existing acceptance
definitions and counterexamples retain their original scope.

| Contract | Conditional consequence | Finding and missing enforcement |
| --- | --- | --- |
| [Initialization](Initialization.lean) | Typed window geometry and distinct selected indices give distinct aligned physical cells, including all GPRs. | AIH-334's EVM validation is implemented and tested; formal correspondence remains external. Geometry comes from the target layout; no copied fixed ceiling, contiguous-window requirement or assumed public memory values. |
| [Decoder](Decoder.lean) | Committed real rows plus unreachable filler and exact active query binding imply the existing logical public decoder membership. | AIH-336 / F09: current zero filler is queryable. This contract describes a corrected setup, including agreement of all cached/uncached consumers; none is derived from the current generator. |
| [Requests](Requests.lean) | A full occurrence ledger plus the existing request binding gives every worker a caller at its native slot, and excludes the zero-clock surplus. | AIH-339 / F03: native cancelling tokens do not supply this ledger. No clock-positivity premise or worker result is added. |
| [Bigint control](BigintABI.lean) | Full x12 binding to one opcode plus carry derives all native control bits and selects the corresponding branch of the existing arithmetic proof. | F02: native acceptance admits controls 0/65537. This is temporary control validation, not pointer validity, whole-call execution or a fix. Carry uses bit six; COPY uses bit seven. |
| [Worker RAM](WorkerRAM.lean) | Native port addresses bound to registers or RAM above ROM are unchanged by public-ROM token interpretation. | F04: accepted ROM-shadow COPY remains a discrepancy. The address-only restriction supplies neither reads nor writes; arbitrary native acceptance has not established it. |

[Public conditional results](../../../Trace/ExternalBoundaries.lean) reuse
the [proof implementations](../../../../Proofs/ExternalBoundary/Initialization.lean).
They expose each temporary premise directly. Original terminal-PC, inactive-row,
invalid-control, zero-clock and ROM-shadow witnesses remain checked under their
old acceptance relations. Passing a temporary contract is not a finding-closure
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
