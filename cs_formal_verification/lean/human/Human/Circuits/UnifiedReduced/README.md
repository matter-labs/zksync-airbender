# Unified reduced circuit review

This directory describes the local witness slices of the unified reduced-machine
artifact: arithmetic, control, binary/shift, memory and selected project-custom
operations or caller requests. The artifact and decoder name the native selectors and the observable
word/state effects against the relevant reference (our RV32 spec, or Clean's). Complete execution and
composition statements are kept in the unified Trace directory.

## Checked results

The [unified execution claims](../../Trace/UnifiedReduced/RVTheorems.lean) prove
the admitted standard and TRIADD/XORROT instructions retire in history-derived
order to native terminal PC/cells, with public ROM bytes and derived reads/bounds.
Those conclusions use the exact declared registry and public boot inputs.
Caller cycles and selected hash windows have separate claims; full mixed caller
retirement and control validity are not implied by local selector mappings.

[Artifact](Artifact.lean) and [Decoder](Decoder.lean) identify the unified columns, selectors and modeled setup.

The unified slices (control, jumps, binary operations, shifts, word memory,
ROM, TRIADD, XORROT) are described by the artifact, decoder and setup; the
[delegation callers](Delegation.lean) have their own module. Standard
instructions and the custom operations are both `RV.step` clauses of our spec
([RV32.lean](../../ISA/RV32.lean)).

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
