# ADD/SUB circuit review

This directory models ADD, ADDI, SUB, LUI and AUIPC rows as operand/result and
architectural PC transitions. Named mappings connect imported limb/register
columns to a selected pre-state and public instruction; the local soundness claim
compares those observables with the original Sail clause. Custom arithmetic,
external-input forms and delegation callers have their own contracts.

1. Read [Theorems](Theorems.lean) for the exact local claim.
2. Read [Model](Model.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow [the selected reference](Reference.lean) and [Artifact](Artifact.lean) for semantics and imported variable placement.

The model retains public initialization, modeled tables and all initialized registers. Bounds, actual reads and preprocessing are derived.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

[Modular](Modular.lean), [external reads](NonDeterminism.lean) and [caller claims](CallerTheorems.lean) have separate scopes. Global inactive-row obligations remain open.

[Family execution](../../Trace/Families/AddSub/Theorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/Soundness.lean) composes the six ordinary families.
