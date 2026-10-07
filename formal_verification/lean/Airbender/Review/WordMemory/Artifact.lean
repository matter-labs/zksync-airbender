import Airbender.Import.Embed

namespace Airbender.WordMemory

-- All retained equations, three range queries, and the conditional ROM query.
-- The caller supplies the native Clean ROM table; its program/setup binding is
-- an explicit interface, and table extraction remains deferred.
import_clean importedConstraints from "../../cs/compiled_circuits/mem_word_only_layout_no_caches_gkr.json" word_memory_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints rom)).length = 27 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints rom)).length = 4 := rfl

/-- Logical IDs used by the local arithmetic proofs. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 10 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 11 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 12 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 17 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 18 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 19 = some "memread_addr[0]" ∧
    importedConstraintsVariableNames.lookup 20 = some "memread_addr[1]" ∧
    importedConstraintsVariableNames.lookup 25 = some "memwrite_addr[0]" ∧
    importedConstraintsVariableNames.lookup 26 = some "memwrite_addr[1]" ∧
    importedConstraintsVariableNames.lookup 33 = some "addr: ofL (L2)" ∧
    importedConstraintsVariableNames.lookup 34 = some "addr: ofH (L2)" ∧
    importedConstraintsVariableNames.lookup 35 = some "flag: are we in rom addr range?" ∧
    importedConstraintsVariableNames.lookup 36 = some "residue (L2)" := by decide

end Airbender.WordMemory
