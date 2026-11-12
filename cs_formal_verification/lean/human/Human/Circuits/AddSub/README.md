# ADD/SUB circuit review

Read `rvModel` and `rvSpec` in [RVModel.lean](RVModel.lean).
`RVSoundnessClaim` states row soundness. The separate `RVSatisfiableClaim` states non-vacuity.

This directory models ADD, ADDI, SUB, LUI and AUIPC rows as operand/result and
architectural PC transitions. Named mappings connect imported limb/register
columns to a selected pre-state and public instruction; the local soundness claim
shows they are one `RV.step` of our spec. Custom arithmetic,
external-input forms and delegation callers have their own contracts.

## Checked results

The [local soundness claims](RVTheorems.lean) prove every represented accepted
ADD/ADDI/SUB/LUI/AUIPC row is one `RV.step` of our spec from the row's pre-state: the destination register
gets the row's result (x0 discards it), the PC gets the row's final PC, nothing else changes.
Public initialization/tables and logical matching/decoding remain premises;
reads, operand/immediate/PC bounds and preprocessing are derived.
The [logical memory result](../../Helpers/Memory/README.md#logical-memory-result)
supplies history consistency; inactive padding and full delegation ABI remain open.

1. Read [RVTheorems](RVTheorems.lean) for the exact local claim.
2. Read [RVModel](RVModel.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow the selected reference and [Artifact](Artifact.lean) for semantics and imported variable placement.

The model retains public initialization, modeled tables and all initialized registers. Bounds, actual reads and preprocessing are derived.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

External reads and [caller claims](RVCallerTheorems.lean) have separate scopes. Global inactive-row obligations remain open.

Open item (decoder-table padding): the [Artifact](Artifact.lean) claim fixes `generic_lookup_padding` = −1
(canonical p − 1). When decoder lookup enforcement is modelled, the decoder table is program rows ∪ unsupported −1
rows ∪ tail rows of that padding (0 when absent); discharging `RVPooledDecoded` then needs "mask coordinate < 512
from the nine Boolean family bits ⇒ no −1 sentinel matches", which zero padding would make false (a phantom 0⁸
row). See [trust and review](../../../../../docs/TRUST_AND_REVIEW.md#modeled-tables-and-logical-arguments).

[Family execution](../../Trace/Families/AddSub/RVTheorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/RVSoundness.lean) composes the six ordinary families.
