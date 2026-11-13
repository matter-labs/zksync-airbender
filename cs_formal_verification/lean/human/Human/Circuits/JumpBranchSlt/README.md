# Jump/branch/SLT circuit review

The comparison, branch, and jump namespaces each define `rvModel` and `rvSpec` in
[RVModel.lean](RVModel.lean). Their `RVSoundnessClaim` statements give row soundness.
Their separate `RVSatisfiableClaim` statements give non-vacuity.

This directory models JAL/JALR, conditional branches and signed/unsigned
comparisons against our RV32 spec. The mappings identify operands,
decoded operations and destination/PC effects. The canonical terminal PC
remains part of the stated interface rather than a
consequence of the local equations alone.

## Checked results

The [comparison, branch and jump soundness claims](RVTheorems.lean) prove each admitted
row is one `RV.step` of our spec (a taken branch or jump lands on a 4-byte aligned target, or no step exists),
with reads and local ranges derived from initialized history. The canonical terminal PC
(`terminalPC`) remains a visible condition; aligned code is the decoder table's fetch guard.
The shared PC-range interface does not yet discharge standalone jump teardown.

1. Read [Theorems](RVTheorems.lean) for the exact local claim.
2. Read [RVModel](RVModel.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow the selected reference and [Artifact](Artifact.lean) for semantics and imported variable placement.

Retain the canonical terminal-PC limbs (the circuit does not range-check the outgoing PC's high limb). There is no machine-configuration premise.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Review [Jump](Jump.lean) alongside [Decoder](Decoder.lean) ([RVDecoder](RVDecoder.lean) for the RV metadata). Binding the terminal PC to teardown stays open.

[Family execution](../../Trace/Families/JumpBranchSlt/RVTheorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/RVSoundness.lean) composes the six ordinary families.
