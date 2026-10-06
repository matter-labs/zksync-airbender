import Airbender.Import.Embed

namespace Airbender.JumpBranchSlt

-- Retained assertions, range16 and four comparison/cleanup queries. Timestamp
-- lookups remain outside this import; fixed-table correspondence is unproved.
import_clean importedConstraints from "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json" comparison_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 26 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 8 := rfl

/-- Numeric roles used by local proofs, checked against imported metadata. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 2 = some "initial_ts[0]" ∧
    importedConstraintsVariableNames.lookup 3 = some "initial_ts[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 7 = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 10 = some "funct3 from decoder" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 13 = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup 14 = some "family_bit[3]" ∧
    importedConstraintsVariableNames.lookup 15 = some "family_bit[4]" ∧
    importedConstraintsVariableNames.lookup 16 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 17 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 18 = some "final_ts[0]" ∧
    importedConstraintsVariableNames.lookup 19 = some "final_ts[1]" ∧
    importedConstraintsVariableNames.lookup 22 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 23 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 26 = some "rs2 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 27 = some "rs2 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 30 = some "rd[0]" ∧
    importedConstraintsVariableNames.lookup 31 = some "rd[1]" ∧
    importedConstraintsVariableNames.lookup 34 = some "Intermediate reg for comparisons[0]" ∧
    importedConstraintsVariableNames.lookup 35 = some "Intermediate reg for comparisons[1]" ∧
    importedConstraintsVariableNames.lookup 36 = some "Intermedaite low for PC computation" ∧
    importedConstraintsVariableNames.lookup 37 = some "Intermedaite boolean 0" ∧
    importedConstraintsVariableNames.lookup 38 = some "Intermedaite boolean 1" ∧
    importedConstraintsVariableNames.lookup 39 = some "Intermedaite boolean 2" ∧
    importedConstraintsVariableNames.lookup 40 = some "Intermedaite boolean 3" ∧
    importedConstraintsVariableNames.lookup 41 = some "Comparison result is zero out var" ∧
    importedConstraintsVariableNames.lookup 42 = some "rs1 sign boolean" ∧
    importedConstraintsVariableNames.lookup 43 = some "slt/branch second-operand sign source" ∧
    importedConstraintsVariableNames.lookup 44 = some "jump resolution variable" ∧
    importedConstraintsVariableNames.lookup 45 = some "should jump if BRANCH opcode" ∧
    importedConstraintsVariableNames.lookup 46 = some "bit 1 for computed next PC" ∧
    importedConstraintsVariableNames.lookup 47 = some "selected rd[0]" ∧
    importedConstraintsVariableNames.lookup 48 = some "selected rd[1]" := by decide

end Airbender.JumpBranchSlt
