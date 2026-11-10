# Jump/branch/SLT circuit review

This directory models JAL/JALR, conditional branches and signed/unsigned
comparisons against their original Sail clauses. The mappings identify operands,
decoded operations and destination/PC effects. Public configuration and
canonical verifier-boundary closure remain part of the stated interface. Local
equations alone do not range every outgoing high PC limb.

## Checked results

The [comparison, branch and jump soundness claims](Theorems.lean) prove original
Sail register/PC effects for each admitted row, with reads and local ranges derived
from initialized history. Aligned code and public ISA/configuration remain
explicit. The [verifier boundary](../../Helpers/Context/VerifierBoundary/README.md)
supplies typed canonical contribution closure. Cancellation against accepted
state matching derives raw terminal bounds; cryptographic enforcement and
Rust/artifact correspondence remain external. The original aliased endpoint
remains accepted locally and is excluded by the new closure contract.

1. Read [Theorems](Theorems.lean) for the exact local claim.
2. Read [Model](Model.lean) for satisfaction, named observable mappings and interface assumptions.
3. Follow [the selected reference](Branch.lean) and [Artifact](Artifact.lean) for semantics and imported variable placement.

Retain aligned public code and the explicit verifier closure. Branch/jump configuration is visible in their models; JALR additionally retains its Machine/MLPE-clear scope.

Follow [shared row context](../../Helpers/Context/README.md),
[decoding](../../Helpers/Decoder/README.md) and [memory history](../../Helpers/Memory/README.md)
only where the model requires them. Per-row reads and bounds are derived from
accepted initialized history. Field minima and inverse conditions are those of
the selected theorem; artifact/import and modeled-table fidelity remain explicit.

Review [Jump](Jump.lean) alongside [Decoder](Decoder.lean). F01 is resolved in the
logical model under the total-verifier boundary binding, without a circuit fix
or an unconditional whole-verifier proof.

[Family execution](../../Trace/Families/JumpBranchSlt/Theorems.lean) is a separate whole-trace claim.
[Pooled execution](../../Trace/Soundness.lean) composes the six ordinary families.
