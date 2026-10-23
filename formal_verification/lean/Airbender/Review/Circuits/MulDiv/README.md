# MUL/DIV circuit review

This directory models MUL, MULHU, DIVU and REMU rows as two operand words, a
selected original Sail operation, and destination/PC effects. The local relation
combines imported constraints with public instruction binding and shared-history
interpretation; zero divisors remain within the admitted division/remainder
behavior.

## Checked results

The [local soundness claims](Theorems.lean) prove the four mapped operations
agree with original Sail destination/PC effects, including zero divisors.
Shared initialization, tables and logical membership/matching derive the operands
and actual reads. Full family execution also binds the terminal PC/cells;
discarded destination writes still route to ADD/SUB.

1. Read [Theorems](Theorems.lean) for the exact local claim.
2. Read [Model](Model.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow [the selected reference](Model.lean) and [Artifact](Artifact.lean) for semantics and imported variable placement.

Initialization and modeled-table conditions stay visible in the model. Original Sail decoding retains configuration reads; discarded destinations route to ADD/SUB.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Check [Decoder](Decoder.lean) against the original public instruction and native metadata.

[Family execution](../../Trace/Families/MulDiv/Theorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/Soundness.lean) composes the six ordinary families.
