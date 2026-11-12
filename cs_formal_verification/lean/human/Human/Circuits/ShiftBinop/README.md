# Shift/binop circuit review

This directory models register/immediate shifts, bitwise operations and REV8 using
native byte/limb encodings and the spec's `RV.alu` and `rev8`. Its mappings identify source
words, decoder-selected preprocessing and destination/PC effects. Initialized
history supplies the actual operands; the representation itself does not assume
their bounds or successful reads.

## Checked results

The [local soundness claims](RVTheorems.lean) prove the admitted shifts/binops
and REV8 are one `RV.step` of our spec with the row's destination/PC effects. Accepted constraints and
initialized history derive input bytes, shift bounds, immediate preprocessing
and reads; public decoding (`RV.decode`) selects the instruction.
The family trace claim composes these effects through terminal PC/cells.

1. Read [Theorems](RVTheorems.lean) for the exact local claim.
2. Read [RVModel](RVModel.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow the selected reference and [Artifact](Artifact.lean) for semantics and imported variable placement.

The model's external condition is public initialization. Operand bytes, shift ranges, immediate preprocessing and actual reads are derived; modeled byte-table fidelity remains separate.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Use [Decoder](Decoder.lean) and [RVDecoder](RVDecoder.lean) for sign/immediate-byte projection and the decoding of REV8.

[Family execution](../../Trace/Families/ShiftBinop/RVTheorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/RVSoundness.lean) composes the six ordinary families.
