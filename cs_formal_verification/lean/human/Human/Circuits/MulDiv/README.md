# MUL/DIV circuit review

This directory models MUL, MULHU, DIVU and REMU rows as two operand words, a
selected operation of `RV.alu`, and destination/PC effects. The local relation
combines imported constraints with public instruction binding and shared-history
interpretation; zero divisors remain within the admitted division/remainder
behavior.

## Checked results

The [local soundness claims](RVTheorems.lean) prove the four mapped operations
are one `RV.step` of our spec with the row's destination/PC effects, including zero divisors
(DIVU by zero is all ones, REMU by zero the dividend).
Shared initialization, tables and logical membership/matching derive the operands
and actual reads. Full family execution also binds the terminal PC/cells.

1. Read [Theorems](RVTheorems.lean) for the exact local claim.
2. Read [RVModel](RVModel.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow the selected reference and [Artifact](Artifact.lean) for semantics and imported variable placement.

Initialization and modeled-table conditions stay visible in the model.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Check [Decoder](Decoder.lean) and [RVDecoder](RVDecoder.lean) against the public instruction (`RV.decode`) and native metadata.

[Family execution](../../Trace/Families/MulDiv/RVTheorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/RVSoundness.lean) composes the six ordinary families.
