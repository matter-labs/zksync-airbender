import Airbender.Import.Embed

namespace Airbender.AddSub

-- The JSON's retained equations and range queries, emitted as native Clean operations.
import_clean importedConstraints from "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json" trace_metadata

/-- Arithmetic, word ranges and the eight native timestamp queries. Decoder and
    global state/memory matching are separate trace obligations. -/
def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[19, 20], #v[2, 3], #v[21, 22],
      #[⟨0, #v[23, 24], 42⟩, ⟨1, #v[27, 28], 43⟩, ⟨2, #v[35, 36], 44⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 30 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 6 := rfl

/-- Guard the roles of the numeric variable IDs used by the proof. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 2 = some "initial_ts[0]" ∧
    importedConstraintsVariableNames.lookup 3 = some "initial_ts[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 7 = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 10 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup 13 = some "family_bit[3]" ∧
    importedConstraintsVariableNames.lookup 14 = some "family_bit[4]" ∧
    importedConstraintsVariableNames.lookup 15 = some "family_bit[5]" ∧
    importedConstraintsVariableNames.lookup 16 = some "family_bit[6]" ∧
    importedConstraintsVariableNames.lookup 17 = some "family_bit[7]" ∧
    importedConstraintsVariableNames.lookup 18 = some "family_bit[8]" ∧
    importedConstraintsVariableNames.lookup 19 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 20 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 21 = some "final_ts[0]" ∧
    importedConstraintsVariableNames.lookup 22 = some "final_ts[1]" ∧
    importedConstraintsVariableNames.lookup 25 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 26 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 27 = some "query 1, read_ts[0]" ∧
    importedConstraintsVariableNames.lookup 28 = some "query 1, read_ts[1]" ∧
    importedConstraintsVariableNames.lookup 29 = some "rs2 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 30 = some "rs2 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 31 = some "rd read_value[0]" ∧
    importedConstraintsVariableNames.lookup 32 = some "rd read_value[1]" ∧
    importedConstraintsVariableNames.lookup 33 = some "rd[0]" ∧
    importedConstraintsVariableNames.lookup 34 = some "rd[1]" ∧
    importedConstraintsVariableNames.lookup 37 = some "Modular ops intermediate comparison reg[0]" ∧
    importedConstraintsVariableNames.lookup 38 = some "Modular ops intermediate comparison reg[1]" ∧
    importedConstraintsVariableNames.lookup 39 = some "intermediate carry for out" ∧
    importedConstraintsVariableNames.lookup 40 = some "carry for out" := by decide

end Airbender.AddSub
