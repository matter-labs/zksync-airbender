# Whole-trace review

This directory states how accepted native histories realize sequences of reference
instruction steps from a public initial state. Its execution contracts include
successful fetch, clause execution and retirement, and its realization claims bind
the resulting PC and tracked cells to native terminal tokens. The selected
registry and profile determine which instructions and custom operations are
admitted.

## Checked results

[`pooled_native_soundness`](Soundness.lean) proves that the six admitted ordinary
families execute from the public Sail state and reach the native final PC and
tracked cells, interpreting native ROM shadows through public bytes.
Initialization/configuration, modeled tables, logical matching/decoding and the
canonical verifier-boundary closure remain inputs; reads, ranges, order and raw
terminal-PC bounds are derived. The closure's cryptographic enforcement and
Rust/artifact correspondence remain external.

[`NonDeterminism.Pooled.native_soundness`](Soundness.lean) proves the same terminal
agreement for the external-read/write-hint extension and the exact stream consumption.
The stream and its port connection are explicit; authentication of the stream is not proved.

[Unified ordinary/custom retirement](UnifiedReduced/README.md#checked-results)
has a separate registry. [Worker spans](Workers/README.md#checked-results) and
[caller composition](Delegation/README.md#checked-results) establish their stated
effects, without closing whole mixed caller retirement or global inactive padding.

Start with [Soundness](Soundness.lean) for the primary six-family standard claim
and its external-stream extension. [Execution](Execution.lean) defines the generic
step relation and `Realizes`: execution reaches the native final PC and tracked cells.
[PooledExecution](PooledExecution.lean) specializes the standard relation.

Read [public pooled inputs](../Helpers/Context/PooledBoundary.lean),
[accepted matching](../Helpers/Context/Model.lean) and
[public decoding](../Helpers/Decoder/PooledProgram.lean) alongside the conclusion.
Native ROM shadows use the explicit public-byte view. The proof derives reads,
bounds, instruction order and actual retirement from one initialized history.

## Choose the composition scope

| Directory | Review it for |
| --- | --- |
| [Families](Families/README.md) | Restricted ADD/SUB + word-memory and standalone family execution. |
| [Workers](Workers/README.md) | Actual worker transport and complete hash protocols. |
| [Delegation](Delegation/README.md) | Caller/worker matching, shared histories and selected spans. |
| [Unified reduced](UnifiedReduced/README.md) | Unified ordinary/custom execution, caller cycles and windows. |

[PooledNonDeterminism](PooledNonDeterminism.lean) adds stream position and exact
consumption. The stream is independently public; circuit authentication of it
is not established.

Check the exact registry and profile of the chosen theorem. Standard clauses use
original Sail; custom clauses use pinned project references. Unchanged Sail's
discarded-load restriction differs from the named Airbender PC-only-NOP profile.

Keep the verifier-boundary contract, active-row scope, public domains and caller ABI
conditions visible. Caller cycles and complete selected spans do not by themselves
prove whole mixed execution with callers. Consult
[current coverage](../../../VERIFICATION_STATUS.md) and
[checked boundaries](../../../TRUST_AND_REVIEW.md#checked-scope-boundaries).

[Padding soundness](Padding.lean) derives the existing restricted, six-family and
unified execution claims from the [external contribution-mask boundary](../Helpers/Context/PaddingBoundary/README.md).
Inactive native PC/write columns need not stutter; exact masked tuple closure
selects the architectural rows. Mixed callers retain their observation scope and
execute-one zero-clock worker effects.
