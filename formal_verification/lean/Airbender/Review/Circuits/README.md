# Circuit review

## Checked results

| Family | Claim and interfaces |
| --- | --- |
| ADD/SUB/LUI/AUIPC | [Guide](AddSub/README.md), [theorems](AddSub/Theorems.lean), [model](AddSub/Model.lean) |
| Word-memory rows | [Guide](WordMemory/README.md), [theorem](WordMemory/Theorems.lean), [model](WordMemory/Model.lean); complete initialized fetched Sail execution under documented ROM/RAM/platform profiles |
| Jump/branch/SLT fixed effects, public/native exported decoding and PC bounds | [Guide](JumpBranchSlt/README.md), [claims](JumpBranchSlt/Theorems.lean), [observables](JumpBranchSlt/Model.lean); [complete fetched execution](../Trace/Families/JumpBranchSlt/Execution.lean) and terminal matching checked under the stated initial CSR profile |
| Unsigned MUL/DIV numerical results and actual masked writes | [Guide](MulDiv/README.md), [claim](MulDiv/Theorems.lean); all four numerical results and zero divisors checked under explicit local interfaces; public decoding/history/original Sail remain open |
| Subword native lookup import | [Guide](SubwordMemory/README.md), [claim](SubwordMemory/Lookups.lean), [artifact](SubwordMemory/Artifact.lean); native metadata/routing, derived offset/trap controls, canonical load values and actual load/store write assembly; decoded normalization/history/execution open |

The remaining v2 families are tracked in the [plan](../../../FORMAL_VERIFICATION_PLAN.md).
Local row soundness and whole execution are distinct milestones.

[Subword public decoding](SubwordMemory/Decoding.lean) now derives original
LB/LH/LBU/LHU/SB/SH fields and bounded actual load writes from native acceptance
and constructed public logical setup membership. All seven full native fixtures
and five decoder rejections pass. Exported decoder fidelity, decoded-key
normalization, initialized history and original subword execution remain open.

[Subword decoder export fidelity](../Trace/Families/SubwordMemory/NativeDecoder.lean)
now checks every row of the actual thirteen-word native export against original
public Sail setup, including negative immediates, x0, unsupported LW and the
complete sentinel tail. This adds no general compiler refinement or initialized
subword execution claim.

[Native subword history](../Trace/Families/SubwordMemory/History.lean) now
connects all three actual mixed register/RAM ports to complete original Clean
history and newest reads from public Sail initialization and native matching.
Readonly shadows/alias refreshes and actual masked writes remain. Native clock
carry/rejection and eight initialized fixtures pass. Original subword execution,
canonical word/key bounds and architectural ROM projection remain separate.
