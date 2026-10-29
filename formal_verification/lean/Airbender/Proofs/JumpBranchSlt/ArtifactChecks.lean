import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.JumpBranchSlt

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[16, 17], #v[2, 3], #v[18, 19],
      #[⟨0, #v[20, 21], 49, none⟩, ⟨1, #v[24, 25], 50, none⟩, ⟨2, #v[32, 33], 51, none⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[20, 21], 49, none⟩, .register 5, #v[22, 23], none⟩,
       ⟨⟨1, #v[24, 25], 50, none⟩, .register 6, #v[26, 27], none⟩,
       ⟨⟨2, #v[32, 33], 51, none⟩, .register 7, #v[28, 29], some #v[30, 31]⟩] :
      Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, #v[8, 9], some 10, #[11, 12, 13, 14, 15]⟩ :
      Trace.DecoderColumns) := rfl

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 26 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 8 := rfl

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
