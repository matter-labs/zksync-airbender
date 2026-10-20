import Human.Circuits.ShiftBinop.Artifact

namespace Airbender.ShiftBinop

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[13, 14], #v[2, 3], #v[15, 16],
      #[⟨0, #v[17, 18], 92⟩, ⟨1, #v[23, 24], 93⟩, ⟨2, #v[33, 34], 94⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[17, 18], 92⟩, .register 5, .u8 #v[19, 20, 21, 22], none⟩,
       ⟨⟨1, #v[23, 24], 93⟩, .register 6, .u8 #v[25, 26, 27, 28], none⟩,
       ⟨⟨2, #v[33, 34], 94⟩, .register 7, #v[29, 30], some #v[31, 32]⟩] :
      Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, #v[8, 9], some 10, #[11, 12]⟩ : Trace.DecoderColumns) := rfl

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 52 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 7 := rfl


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
