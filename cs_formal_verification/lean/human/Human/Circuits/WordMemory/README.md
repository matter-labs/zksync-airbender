# Word memory circuit review

This directory models supported LW/SW rows: effective address, transferred word,
register or memory update, and PC retirement. Its mappings distinguish load/store
observables and interpret them through the original Sail memory clause on the
declared platform. Native ROM-shadow columns and independent public ROM bytes are
kept separate.

## Checked results

The [local soundness claims](../../../../slop/Slop/Final/Circuits/WordMemory/Theorems.lean) prove effective addresses, actual
LW/SW register/memory effects and PC retirement under the ordinary-domain and
flat-memory configuration. Reads and address/word bounds follow from accepted
initialized history. Public-ROM interpretation is connected explicitly; the
discarded-LW profile remains distinct from unchanged Sail.

1. Read [Theorems](../../../../slop/Slop/Final/Circuits/WordMemory/Theorems.lean) for the exact local claim.
2. Read [Model](Model.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow [the selected reference](Model.lean) and [Artifact](Artifact.lean) for semantics and imported variable placement.

Retain the public tracked domain, ordinary addresses, flat-memory configuration and modeled ROM binding. Native zero ROM shadows and public byte reads are distinct.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

LW-to-x0 routes to the named Airbender PC-only-NOP profile. Unchanged Sail excludes that deviation; the checked sparse-memory fixture demonstrates the difference.

[Family execution](../../../../slop/Slop/Final/Trace/Families/AddSub/Theorems.lean) is a separate whole-trace claim.
[Pooled execution](../../../../slop/Slop/Final/Trace/Soundness.lean) composes the six ordinary families.
