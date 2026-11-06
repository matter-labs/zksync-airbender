# Jump/branch/SLT circuit review

This directory models JAL/JALR, conditional branches and signed/unsigned
comparisons against their original Sail clauses. The mappings identify operands,
decoded operations and destination/PC effects. Public configuration and
terminal-PC normalization remain part of the stated interface rather than
consequences of the local equations alone.

## Checked results

The [comparison, branch and jump soundness claims](../../../../slop/Slop/Final/Circuits/JumpBranchSlt/Theorems.lean) prove original
Sail register/PC effects for each admitted row, with reads and local ranges derived
from initialized history. Aligned code, public ISA/configuration and canonical
terminal PC remain visible conditions. The shared PC-range interface does not
yet discharge standalone jump teardown; the checked aliased endpoint remains.

1. Read [Theorems](../../../../slop/Slop/Final/Circuits/JumpBranchSlt/Theorems.lean) for the exact local claim.
2. Read [Model](Model.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow [the selected reference](Branch.lean) and [Artifact](Artifact.lean) for semantics and imported variable placement.

Retain aligned public code and canonical terminal-PC limbs. Branch/jump configuration is the machine's `Configured` initial state (reset privilege, `misa`, landing-pad state), visible in their models.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Review [Jump](Jump.lean) alongside [Decoder](Decoder.lean). A checked noncanonical JAL endpoint keeps terminal-PC teardown binding open.

[Family execution](../../../../slop/Slop/Final/Trace/Families/JumpBranchSlt/Theorems.lean) is a separate whole-trace claim.
[Pooled execution](../../../../slop/Slop/Final/Trace/Soundness.lean) composes the six ordinary families.
