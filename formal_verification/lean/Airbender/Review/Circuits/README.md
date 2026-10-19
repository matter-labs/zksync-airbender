# Circuit review

## Checked results

| Family | Claim and interfaces |
| --- | --- |
| ADD/SUB/LUI/AUIPC | [Guide](AddSub/README.md), [theorems](AddSub/Theorems.lean), [model](AddSub/Model.lean) |
| Word-memory rows | [Guide](WordMemory/README.md), [theorem](WordMemory/Theorems.lean), [model](WordMemory/Model.lean); complete initialized fetched Sail execution under documented ROM/RAM/platform profiles |
| Jump/branch/SLT fixed effects, public/native exported decoding and PC bounds | [Guide](JumpBranchSlt/README.md), [claims](JumpBranchSlt/Theorems.lean), [observables](JumpBranchSlt/Model.lean); [complete fetched execution](../Trace/Families/JumpBranchSlt/Execution.lean) and terminal matching checked under the stated initial CSR profile |
| Unsigned MUL/DIV artifact and paired-byte queries | [Guide](MulDiv/README.md), [artifact](MulDiv/Artifact.lean); native table data and byte bounds checked, instruction semantics/history/execution remain open |

The remaining v2 families are tracked in the [plan](../../../FORMAL_VERIFICATION_PLAN.md).
Local row soundness and whole execution are distinct milestones.
