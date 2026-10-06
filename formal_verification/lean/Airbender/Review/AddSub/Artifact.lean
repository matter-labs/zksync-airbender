import Airbender.Import.Embed

namespace Airbender.AddSub

-- The JSON's retained equations and range queries, emitted as native Clean operations.
import_clean importedConstraints from "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json"

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 30 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 6 := rfl

/-- Guard the roles of the numeric variable IDs used by the proof. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 10 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 19 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 20 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 25 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 26 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 29 = some "rs2 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 30 = some "rs2 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 33 = some "rd[0]" ∧
    importedConstraintsVariableNames.lookup 34 = some "rd[1]" ∧
    importedConstraintsVariableNames.lookup 37 = some "Modular ops intermediate comparison reg[0]" ∧
    importedConstraintsVariableNames.lookup 38 = some "Modular ops intermediate comparison reg[1]" ∧
    importedConstraintsVariableNames.lookup 39 = some "intermediate carry for out" ∧
    importedConstraintsVariableNames.lookup 40 = some "carry for out" := by decide

end Airbender.AddSub
