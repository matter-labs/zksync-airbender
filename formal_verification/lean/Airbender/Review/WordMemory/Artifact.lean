import Airbender.Import.Embed

namespace Airbender.WordMemory

-- All retained equations, three range queries, and the conditional ROM query.
-- The caller supplies the native Clean ROM table; its program/setup binding is
-- an explicit interface, and table extraction remains deferred.
import_clean importedConstraints from "../../cs/compiled_circuits/mem_word_only_layout_no_caches_gkr.json" word_memory_lookups trace_metadata

def clockConstraints {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints rom ++ importedConstraintsTimestampLookups

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[11, 12], #v[2, 3], #v[13, 14],
      #[⟨0, #v[15, 16], 46⟩, ⟨1, #v[21, 22], 47⟩, ⟨2, #v[27, 28], 48⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[15, 16], 46⟩, .register 5, #v[17, 18], none⟩,
       ⟨⟨1, #v[21, 22], 47⟩, .mixed 10 true #v[19, 20], #v[23, 24], none⟩,
       ⟨⟨2, #v[27, 28], 48⟩, .mixed 10 false #v[25, 26], #v[29, 30], some #v[31, 32]⟩] :
      Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, #v[8, 9], none, #[10]⟩ : Trace.DecoderColumns) := rfl

namespace Variables
abbrev initialPCLo := 0
abbrev initialPCHi := 1
abbrev execute := 4
abbrev rs1Index := 5
abbrev rs2Index := 6
abbrev rdIndex := 7
abbrev immediateLo := 8
abbrev immediateHi := 9
abbrev storeSelector := 10
abbrev finalPCLo := 11
abbrev finalPCHi := 12
abbrev sourceLo := 17
abbrev sourceHi := 18
abbrev readAddressLo := 19
abbrev readAddressHi := 20
abbrev readDataLo := 23
abbrev readDataHi := 24
abbrev writeAddressLo := 25
abbrev writeAddressHi := 26
abbrev writeDataLo := 31
abbrev writeDataHi := 32
abbrev romSelector := 35
end Variables

theorem constraint_count {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints rom)).length = 27 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints rom)).length = 4 := rfl

/-- Logical IDs used by the local arithmetic proofs. -/
theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 5 = some "rs1 index from decoder" ∧
    importedConstraintsVariableNames.lookup 6 = some "rs2 index from decoder" ∧
    importedConstraintsVariableNames.lookup 7 = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 10 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 11 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 12 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 17 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 18 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 19 = some "memread_addr[0]" ∧
    importedConstraintsVariableNames.lookup 20 = some "memread_addr[1]" ∧
    importedConstraintsVariableNames.lookup 23 = some "mem/rs2 read read_value[0]" ∧
    importedConstraintsVariableNames.lookup 24 = some "mem/rs2 read read_value[1]" ∧
    importedConstraintsVariableNames.lookup 25 = some "memwrite_addr[0]" ∧
    importedConstraintsVariableNames.lookup 26 = some "memwrite_addr[1]" ∧
    importedConstraintsVariableNames.lookup 31 = some "mem/rd write write_value[0]" ∧
    importedConstraintsVariableNames.lookup 32 = some "mem/rd write write_value[1]" ∧
    importedConstraintsVariableNames.lookup 33 = some "addr: ofL (L2)" ∧
    importedConstraintsVariableNames.lookup 34 = some "addr: ofH (L2)" ∧
    importedConstraintsVariableNames.lookup 35 = some "flag: are we in rom addr range?" ∧
    importedConstraintsVariableNames.lookup 36 = some "residue (L2)" ∧
    importedConstraintsVariableNames.lookup 39 = some "final lookup input (L3)" ∧
    importedConstraintsVariableNames.lookup 41 = some "final lookup output1 (L3)" ∧
    importedConstraintsVariableNames.lookup 43 = some "final lookup output2 (L3)" ∧
    importedConstraintsVariableNames.lookup 45 = some "final lookup table_id (L3)" := by decide

end Airbender.WordMemory
