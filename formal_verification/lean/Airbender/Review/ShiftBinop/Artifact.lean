import Airbender.Import.Embed

namespace Airbender.ShiftBinop

-- All retained equations, both range queries and all five dynamic-tag lookups.
-- Decoder, memory/timestamp arguments and fixed-table provenance remain external.
import_clean importedConstraints from "../../cs/compiled_circuits/shift_binop_layout_no_caches_gkr.json" shift_binop_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 52 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 7 := rfl

/-- Check the roles used by the local flag/PC proofs against imported metadata. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 13 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 14 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 52 = some "input 0 for binary sign ext/trucate shift" ∧
    importedConstraintsVariableNames.lookup 55 = some "table ID for binary sign ext/trucate shift" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.ShiftBinop
