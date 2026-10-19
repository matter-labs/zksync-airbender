# Circuit review

## Checked results

| Family | Claim and interfaces |
| --- | --- |
| ADD/SUB/LUI/AUIPC | [Guide](AddSub/README.md), [theorems](AddSub/Theorems.lean), [model](AddSub/Model.lean) |
| Word-memory rows | [Guide](WordMemory/README.md), [theorem](WordMemory/Theorems.lean), [model](WordMemory/Model.lean); complete initialized fetched Sail execution under documented ROM/RAM/platform profiles |
| Jump/branch/SLT fixed effects, public/native exported decoding and PC bounds | [Guide](JumpBranchSlt/README.md), [claims](JumpBranchSlt/Theorems.lean), [observables](JumpBranchSlt/Model.lean); [complete fetched execution](../Trace/Families/JumpBranchSlt/Execution.lean) and terminal matching checked under the stated initial CSR profile |
| Unsigned MUL/DIV numerical results and actual masked writes | [Guide](MulDiv/README.md), [claim](MulDiv/Theorems.lean); all four numerical results and zero divisors checked under explicit local interfaces; public decoding/history/original Sail remain open |

The remaining v2 families are tracked in the [plan](../../../FORMAL_VERIFICATION_PLAN.md).
Local row soundness and whole execution are distinct milestones.
