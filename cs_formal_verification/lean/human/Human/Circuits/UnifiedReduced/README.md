# Unified reduced circuit review

This directory describes the local witness slices of the unified reduced-machine
artifact: arithmetic, control, binary/shift, memory and selected project-custom
operations or caller requests. Models name the native selectors and observable
word/state effects against the relevant reference. Complete execution and
composition statements are kept in the unified Trace directory.

## Checked results

The [unified execution claims](../../../../slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean) prove
the admitted standard and TRIADD/XORROT instructions retire in history-derived
order to native terminal PC/cells, with public ROM bytes and derived reads/bounds.
Those conclusions use the exact declared registry and public profile inputs.
Caller cycles and selected hash windows have separate claims; full mixed caller
retirement and control validity are not implied by local selector mappings.

Start with Model for the arithmetic slice's observable words,
selected pre-state and public instruction binding. [Artifact](Artifact.lean)
and [Decoder](Decoder.lean) identify the unified columns, selectors and modeled setup.

Read the slice being reviewed: [`control`](Control.lean), jumps,
[binary](Binary.lean), shifts, word memory,
ROM, TRIADD, XORROT,
or [delegation callers](Delegation.lean). Standard clauses use original Sail;
custom operations use the pinned project reference.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

[Unified shared context](../../Helpers/UnifiedReduced/README.md) binds public
initialization, current fetch and matched worker histories.
[Unified trace review](../../Trace/UnifiedReduced/README.md) owns mixed retirement,
caller cycles and selected hash windows. Those claims have different registries
and do not close full custom-CSR ABI or inactive-padding obligations.
