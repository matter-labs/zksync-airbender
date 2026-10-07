import Airbender.Import.Embed

namespace Airbender.JumpBranchSlt

-- Retained assertions, range16 and four comparison/cleanup queries. Timestamp
-- lookups remain outside this import; fixed-table correspondence is unproved.
import_clean importedConstraints from "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json" comparison_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 26 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 8 := rfl

-- Named columns used by the review contracts. The metadata guard below checks
-- their locations; the decoder assumptions supply the selectors' meaning.
namespace Variables
abbrev initialPCLo : Nat := 0
abbrev initialPCHi : Nat := 1
abbrev execute : Nat := 4
abbrev rs1Index : Nat := 5
abbrev rs2Index : Nat := 6
abbrev rdIndex : Nat := 7
abbrev immediateLo : Nat := 8
abbrev immediateHi : Nat := 9
abbrev conditionTag : Nat := 10
abbrev jalSelector : Nat := 11
abbrev jalrSelector : Nat := 12
abbrev comparisonSelector : Nat := 13
abbrev branchSelector : Nat := 14
abbrev discardedSelector : Nat := 15
abbrev finalPCLo : Nat := 16
abbrev finalPCHi : Nat := 17
abbrev rs1Lo : Nat := 22
abbrev rs1Hi : Nat := 23
abbrev rs2Lo : Nat := 26
abbrev rs2Hi : Nat := 27
abbrev destinationLo : Nat := 30
abbrev destinationHi : Nat := 31
end Variables

/-- Review names and numeric proof roles agree with imported metadata. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup Variables.initialPCLo = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup Variables.initialPCHi = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 2 = some "initial_ts[0]" ∧
    importedConstraintsVariableNames.lookup 3 = some "initial_ts[1]" ∧
    importedConstraintsVariableNames.lookup Variables.execute = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup Variables.rs1Index = some "rs1 index from decoder" ∧
    importedConstraintsVariableNames.lookup Variables.rs2Index = some "rs2 index from decoder" ∧
    importedConstraintsVariableNames.lookup Variables.rdIndex = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup Variables.immediateLo = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup Variables.immediateHi = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup Variables.conditionTag = some "funct3 from decoder" ∧
    importedConstraintsVariableNames.lookup Variables.jalSelector = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup Variables.jalrSelector = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup Variables.comparisonSelector = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup Variables.branchSelector = some "family_bit[3]" ∧
    importedConstraintsVariableNames.lookup Variables.discardedSelector = some "family_bit[4]" ∧
    importedConstraintsVariableNames.lookup Variables.finalPCLo = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup Variables.finalPCHi = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 18 = some "final_ts[0]" ∧
    importedConstraintsVariableNames.lookup 19 = some "final_ts[1]" ∧
    importedConstraintsVariableNames.lookup Variables.rs1Lo = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup Variables.rs1Hi = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup Variables.rs2Lo = some "rs2 read_value[0]" ∧
    importedConstraintsVariableNames.lookup Variables.rs2Hi = some "rs2 read_value[1]" ∧
    importedConstraintsVariableNames.lookup Variables.destinationLo = some "rd[0]" ∧
    importedConstraintsVariableNames.lookup Variables.destinationHi = some "rd[1]" ∧
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
