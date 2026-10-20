# Subword memory circuit review

This directory models byte/halfword loads and stores through their containing
aligned word cells. The observable relation includes selected data, signed
extension, merged store contents and PC effects, with old-cell and
transferred-data mappings distinguished. Original Sail clauses supply the
architectural behavior.

## Checked results

The [local soundness claims](../../../../slop/Slop/Final/Circuits/SubwordMemory/Theorems.lean) prove aligned-cell address, selected
load data or merged store word, sign/width behavior and PC effects against Sail.
Public initialization/tables and ordinary-domain/configuration conditions remain;
history derives reads, ranges and byte/halfword/word transport.
The standalone RAM trace and pooled RAM/ROM claim have distinct scopes.

1. Read [Theorems](../../../../slop/Slop/Final/Circuits/SubwordMemory/Theorems.lean) for the exact local claim.
2. Read [Model](Model.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow [the selected reference](Model.lean) and [Artifact](Artifact.lean) for semantics and imported variable placement.

Retain public initialization/table binding, ordinary addresses and flat-memory configuration. Check aligned-cell observables separately from the accessed byte/halfword.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Use [Decoder](Decoder.lean) for width/sign/immediate projection. The standalone trace theorem covers RAM; pooled composition separately includes public-ROM transport.

[Family execution](../../../../slop/Slop/Final/Trace/Families/SubwordMemory/Theorems.lean) is a separate whole-trace claim.
[Pooled execution](../../../../slop/Slop/Final/Trace/Soundness.lean) composes the six ordinary families.
