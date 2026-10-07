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
    importedConstraintsVariableNames.lookup 5 = some "rs1 index from decoder" ∧
    importedConstraintsVariableNames.lookup 6 = some "rs2 index from decoder" ∧
    importedConstraintsVariableNames.lookup 7 = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 10 = some "funct3 from decoder" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 13 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 14 = some "final_pc[1]" ∧
    (∀ i : Fin 4, importedConstraintsVariableNames.lookup (19 + i.val) =
      some (["rs1 read_value_u8[0]", "rs1 read_value_u8[1]", "rs1 read_value_u8[2]",
        "rs1 read_value_u8[3]"].get i)) ∧
    (∀ i : Fin 4, importedConstraintsVariableNames.lookup (25 + i.val) =
      some (["rs2 read_value_u8[0]", "rs2 read_value_u8[1]", "rs2 read_value_u8[2]",
        "rs2 read_value_u8[3]"].get i)) ∧
    importedConstraintsVariableNames.lookup 31 = some "rd[0]" ∧
    importedConstraintsVariableNames.lookup 32 = some "rd[1]" ∧
    (∀ i : Fin 17, importedConstraintsVariableNames.lookup (35 + i.val) =
      some s!"scratch space {i.val}") ∧
    importedConstraintsVariableNames.lookup 52 = some "input 0 for binary sign ext/trucate shift" ∧
    importedConstraintsVariableNames.lookup 55 = some "table ID for binary sign ext/trucate shift" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.ShiftBinop
