import Airbender.Import.Embed

namespace Airbender.UnifiedReduced

-- All retained equations, ranges and five pooled lookup sets. The caller supplies
-- the tagged setup table; decoder and global memory arguments remain external.
set_option maxRecDepth 8192
import_clean importedConstraints from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json" unified_reduced_lookups trace_metadata

/-- Retained equations, modeled setup queries and the eight native clock queries.
    Decoder membership and global state/memory matching are separate obligations. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[30, 31], #v[2, 3], #v[32, 33],
      #[⟨0, #v[34, 35], 131⟩, ⟨1, #v[40, 41], 132⟩, ⟨2, #v[46, 47], 133⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[34, 35], 131⟩, .register 5, #v[36, 37], none⟩,
       ⟨⟨1, #v[40, 41], 132⟩, .mixed 28 false #v[38, 39], #v[42, 43], none⟩,
       ⟨⟨2, #v[46, 47], 133⟩, .mixed 29 false #v[44, 45], #v[48, 49], some #v[50, 51]⟩] :
      Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, #v[8, 9], some 10,
      #[11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]⟩ :
      Trace.DecoderColumns) := rfl

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 129 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 18 := rfl

namespace Variables
abbrev initialPCLo := 0
abbrev initialPCHi := 1
abbrev execute := 4
abbrev jalSelector := 21
abbrev jalrSelector := 22
abbrev comparisonSelector := 23
abbrev branchSelector := 24
abbrev finalPCLo := 30
abbrev finalPCHi := 31
abbrev pcCarry := 128
abbrev pcGate := 129
abbrev familyDispatch := 130
abbrev dispatchColumns := #v[11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29]
end Variables

theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 7 = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 13 = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup 14 = some "family_bit[3]" ∧
    importedConstraintsVariableNames.lookup 15 = some "family_bit[4]" ∧
    importedConstraintsVariableNames.lookup 16 = some "family_bit[5]" ∧
    importedConstraintsVariableNames.lookup 17 = some "family_bit[6]" ∧
    importedConstraintsVariableNames.lookup 18 = some "family_bit[7]" ∧
    importedConstraintsVariableNames.lookup 19 = some "family_bit[8]" ∧
    importedConstraintsVariableNames.lookup 20 = some "family_bit[9]" ∧
    importedConstraintsVariableNames.lookup 21 = some "family_bit[10]" ∧
    importedConstraintsVariableNames.lookup 22 = some "family_bit[11]" ∧
    importedConstraintsVariableNames.lookup 23 = some "family_bit[12]" ∧
    importedConstraintsVariableNames.lookup 24 = some "family_bit[13]" ∧
    importedConstraintsVariableNames.lookup 25 = some "family_bit[14]" ∧
    importedConstraintsVariableNames.lookup 26 = some "family_bit[15]" ∧
    importedConstraintsVariableNames.lookup 27 = some "family_bit[16]" ∧
    importedConstraintsVariableNames.lookup 28 = some "family_bit[17]" ∧
    importedConstraintsVariableNames.lookup 29 = some "family_bit[18]" ∧
    importedConstraintsVariableNames.lookup 30 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 31 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 36 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 37 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 42 = some "rs2/mem read read_value[0]" ∧
    importedConstraintsVariableNames.lookup 43 = some "rs2/mem read read_value[1]" ∧
    importedConstraintsVariableNames.lookup 48 = some "rd/mem write read_value[0]" ∧
    importedConstraintsVariableNames.lookup 49 = some "rd/mem write read_value[1]" ∧
    importedConstraintsVariableNames.lookup 50 = some "rd/mem write write_value[0]" ∧
    importedConstraintsVariableNames.lookup 51 = some "rd/mem write write_value[1]" ∧
    importedConstraintsVariableNames.lookup 52 = some "shared scratch bool[0]" ∧
    importedConstraintsVariableNames.lookup 53 = some "shared scratch bool[1]" ∧
    importedConstraintsVariableNames.lookup 54 = some "shared scratch bool[2]" ∧
    importedConstraintsVariableNames.lookup 55 = some "shared scratch bool[3]" ∧
    importedConstraintsVariableNames.lookup 56 = some "shared scratch bool[4]" ∧
    importedConstraintsVariableNames.lookup 83 = some "is_jal_or_jalr_writes_rd" ∧
    importedConstraintsVariableNames.lookup 84 = some "is_slt_writes_rd" ∧
    importedConstraintsVariableNames.lookup 85 = some "gate_fam2_rd_zero" ∧
    importedConstraintsVariableNames.lookup 87 = some "gate_fam4_rom_read" ∧
    importedConstraintsVariableNames.lookup 128 = some "unified pc-bump carry" ∧
    importedConstraintsVariableNames.lookup 129 = some "unified pc-bump gate" ∧
    importedConstraintsVariableNames.lookup 130 = some "unified family-dispatch one-hot" ∧
    importedConstraintsVariableNames.lookup 131 = some "query 0, interim ts borrow" ∧
    importedConstraintsVariableNames.lookup 132 = some "query 1, interim ts borrow" ∧
    importedConstraintsVariableNames.lookup 133 = some "query 2, interim ts borrow" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.UnifiedReduced
