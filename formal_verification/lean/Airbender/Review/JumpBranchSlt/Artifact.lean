import Airbender.Import.Embed

namespace Airbender.JumpBranchSlt

-- Generic/timestamp lookups are not emitted by this import; instruction claims
-- need their semantics. This partial artifact contains retained assertions and range16 queries.
import_clean importedConstraints from "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json"

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 26 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 4 := rfl

/-- Numeric roles used by local proofs, checked against imported metadata. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 2 = some "initial_ts[0]" ∧
    importedConstraintsVariableNames.lookup 3 = some "initial_ts[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 13 = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup 14 = some "family_bit[3]" ∧
    importedConstraintsVariableNames.lookup 15 = some "family_bit[4]" ∧
    importedConstraintsVariableNames.lookup 17 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 18 = some "final_ts[0]" ∧
    importedConstraintsVariableNames.lookup 19 = some "final_ts[1]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 22 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 23 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 26 = some "rs2 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 27 = some "rs2 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 34 = some "Intermediate reg for comparisons[0]" ∧
    importedConstraintsVariableNames.lookup 35 = some "Intermediate reg for comparisons[1]" ∧
    importedConstraintsVariableNames.lookup 36 = some "Intermedaite low for PC computation" ∧
    importedConstraintsVariableNames.lookup 37 = some "Intermedaite boolean 0" ∧
    importedConstraintsVariableNames.lookup 38 = some "Intermedaite boolean 1" := by decide

end Airbender.JumpBranchSlt
