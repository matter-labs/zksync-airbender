# Subword memory circuit review

This directory models byte/halfword loads and stores through their containing
aligned word cells. The observable relation includes selected data, signed
extension, merged store contents and PC effects, with old-cell and
transferred-data mappings distinguished. The spec's `RV.step` (aligned
loads from ROM or RAM, stores only in RAM) supplies the architectural behavior.

## Checked results

The [local soundness claims](RVTheorems.lean) prove aligned-cell address, selected
load data or merged store word, sign/width behavior and PC effects against `RV.step`.
Public initialization/tables remain premises;
history derives reads, ranges and byte/halfword/word transport.
The standalone RAM trace and pooled RAM/ROM claim have distinct scopes.

1. Read [Theorems](RVTheorems.lean) for the exact local claim.
2. Read [RVModel](RVModel.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow the selected reference and [Artifact](Artifact.lean) for semantics and imported variable placement.

Retain public initialization/table binding. There is no machine-configuration or Sail memory-map premise. Check aligned-cell observables separately from the accessed byte/halfword.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Use [Decoder](Decoder.lean) and [RVDecoder](RVDecoder.lean) for width/sign/immediate projection. The standalone trace theorem covers RAM; pooled composition separately includes public-ROM transport.

[Family execution](../../Trace/Families/SubwordMemory/RVTheorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/RVSoundness.lean) composes the six ordinary families.
