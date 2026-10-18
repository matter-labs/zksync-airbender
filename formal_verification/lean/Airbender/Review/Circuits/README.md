# Circuit review

## Checked results

| Family | Claim and interfaces |
| --- | --- |
| ADD/SUB/LUI/AUIPC | [Guide](AddSub/README.md), [theorems](AddSub/Theorems.lean), [model](AddSub/Model.lean) |
| Word-memory rows | [Guide](WordMemory/README.md), [theorem](WordMemory/Theorems.lean), [model](WordMemory/Model.lean); native transfers/address arithmetic, Sail assembly pending |
| Jump/branch/SLT fixed effects and supported-mask PC bounds | [Guide](JumpBranchSlt/README.md), [claims](JumpBranchSlt/Theorems.lean), [observables](JumpBranchSlt/Model.lean); public decoding and original Sail execution remain open |

The remaining v2 families are tracked in the [plan](../../../FORMAL_VERIFICATION_PLAN.md).
Local row soundness and whole execution are distinct milestones.
