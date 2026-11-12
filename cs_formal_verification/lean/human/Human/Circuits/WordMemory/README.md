# Word memory circuit review

This directory models supported LW/SW rows: effective address, transferred word,
register or memory update, and PC retirement. Its mappings distinguish load/store
observables and interpret them through the spec's LW/SW clauses (`RV.exec`: aligned accesses, SW only in RAM).
Native ROM-shadow columns and independent public ROM bytes are kept separate.

## Checked results

The [local soundness claims](RVTheorems.lean) prove effective addresses, LW/SW
register/memory effects and PC retirement as one `RV.step` of our spec, which
exists only for aligned accesses and, for SW, RAM addresses. Reads and address/word bounds follow
from accepted initialized history. Public-ROM interpretation is connected explicitly
(the modeled word-ROM table is the ROM image).

1. Read [Theorems](RVTheorems.lean) for the exact local claim.
2. Read [RVModel](RVModel.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow the selected reference and [Artifact](Artifact.lean) for semantics and imported variable placement.

Retain the public tracked domain and modeled ROM binding. There is no machine-configuration or Sail memory-map premise. Native zero ROM shadows and public byte reads are distinct.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

A load into x0 only advances the PC in the spec (Airbender's rule), so the claims need no load restriction.

[Family execution](../../Trace/Families/AddSub/RVTheorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/RVSoundness.lean) composes the six ordinary families.
