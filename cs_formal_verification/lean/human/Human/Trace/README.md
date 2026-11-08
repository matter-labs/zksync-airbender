# Whole-trace review

This directory states how accepted native histories realize sequences of reference
instruction steps from a public initial state. Its execution contracts include
successful fetch, clause execution and retirement, and its realization claims bind
the resulting PC and tracked cells to native terminal tokens. The selected
registry and profile determine which instructions and custom operations are
admitted.

## Checked results

[`rv_pooled_native_soundness`](../../../slop/Slop/Final/Trace/RVSoundness.lean) proves that the six admitted ordinary
families, booted from the public `RV.State`, are a run of `RV.run` reaching the native final PC and
tracked cells. The RAM seeds are the inits/teardowns Init tokens (`RVPooledBootInputs`), the modeled
ROM tables are built from the ROM image, and native ROM-shadow cells are shadow RAM.
Initialization, modeled tables, logical matching/decoding and the
unresolved jump terminal-PC condition remain inputs; reads, ranges and order are derived.

[`NonDeterminism.Pooled.rv_native_soundness`](../../../slop/Slop/Final/Trace/RVSoundness.lean) proves the same terminal
agreement for the external-read/write-hint extension and the exact stream consumption.
The stream (`RV.State.input`) and its port connection are explicit; authentication of the stream is not proved.

[`no_zero_timestamp_writes`](../../../slop/Slop/Final/Trace/ZeroTimestamp.lean) (statements in
[ZeroTimestamp](ZeroTimestamp.lean), one per pooled CPU trace, unified machine, delegation workers and split Keccak
workers) proves that no row of these circuits writes a memory token at timestamp 0: CPU rows write at clock four or
later after boot, delegation rows at their invocation clock plus two. So only the init circuits produce
timestamp-0 values; those circuits and cross-chunk clock chaining are not formalised, and RAM starting at zero stays
an initial-state condition.

[Unified ordinary/custom retirement](UnifiedReduced/README.md#checked-results)
has a separate registry. [Worker spans](Workers/README.md#checked-results) and
[caller composition](Delegation/README.md#checked-results) establish their stated
effects, without closing whole mixed caller retirement or global inactive padding.

Start with [RVSoundness](RVSoundness.lean) for the primary six-family standard claim
and its external-stream extension. [RVExecution](RVExecution.lean) defines `RVRealizes`:
some number of `RV.step`s from the public state reach the native final PC and tracked cells.

Read the [public boot inputs](../Helpers/Context/RVPooledBoundary.lean),
[accepted matching](../Helpers/Context/Model.lean) and
[public decoding](../Helpers/Decoder/RVPooledProgram.lean) alongside the conclusion.
The proof derives reads, bounds, instruction order and actual retirement from one initialized history.

## Choose the composition scope

| Directory | Review it for |
| --- | --- |
| [Families](Families/README.md) | Restricted ADD/SUB + word-memory and standalone family execution. |
| [Workers](Workers/README.md) | Actual worker transport and complete hash protocols. |
| [Delegation](Delegation/README.md) | Caller/worker matching, shared histories and selected spans. |
| [Unified reduced](UnifiedReduced/README.md) | Unified ordinary/custom execution, caller cycles and windows. |

The external-input claim adds stream position and exact
consumption. The stream is independently public; circuit authentication of it
is not established.

Check the exact registry of the chosen theorem. Standard and custom instructions are
`RV.step` clauses of our spec; a load into x0 only advances the PC there, so no load restriction applies.
Teardown values are bounded only under an open item ([TeardownBounds](TeardownBounds.lean));
every write is range-checked ([WritesRangeChecked](WritesRangeChecked.lean)).

Keep terminal-PC normalization, active-row scope, public domains and caller ABI
conditions visible. Caller cycles and complete selected spans do not by themselves
prove whole mixed execution with callers. Consult
[current coverage](../../../../docs/VERIFICATION_STATUS.md) and
[checked boundaries](../../../../docs/TRUST_AND_REVIEW.md#checked-scope-boundaries).
