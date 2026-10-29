import Airbender.Review.Circuits.SubwordMemory.Artifact

namespace Airbender.SubwordMemory

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[13, 14], #v[2, 3], #v[15, 16],
      #[⟨0, #v[17, 18], 62, none⟩, ⟨1, #v[23, 24], 63, none⟩, ⟨2, #v[29, 30], 64, none⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[17, 18], 62, none⟩, .register 5, #v[19, 20], none⟩,
       ⟨⟨1, #v[23, 24], 63, none⟩, .mixed 10 true #v[21, 22], #v[25, 26], none⟩,
       ⟨⟨2, #v[29, 30], 64, none⟩, .mixed 10 false #v[27, 28], #v[31, 32], some #v[33, 34]⟩] :
      Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, #v[8, 9], none, #[10, 11, 12]⟩ : Trace.DecoderColumns) := rfl

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 43 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 7 := rfl

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
    importedConstraintsVariableNames.lookup 11 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup 13 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 14 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 19 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 20 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 21 = some "memread_addr[0]" ∧
    importedConstraintsVariableNames.lookup 22 = some "memread_addr[1]" ∧
    importedConstraintsVariableNames.lookup 25 = some "mem/rs2 read read_value[0]" ∧
    importedConstraintsVariableNames.lookup 26 = some "mem/rs2 read read_value[1]" ∧
    importedConstraintsVariableNames.lookup 27 = some "memwrite_addr[0]" ∧
    importedConstraintsVariableNames.lookup 28 = some "memwrite_addr[1]" ∧
    importedConstraintsVariableNames.lookup 31 = some "mem/rd write read_value[0]" ∧
    importedConstraintsVariableNames.lookup 32 = some "mem/rd write read_value[1]" ∧
    importedConstraintsVariableNames.lookup 33 = some "mem/rd write write_value[0]" ∧
    importedConstraintsVariableNames.lookup 34 = some "mem/rd write write_value[1]" ∧
    importedConstraintsVariableNames.lookup 35 = some "address bit0" ∧
    importedConstraintsVariableNames.lookup 36 = some "address bit1" ∧
    importedConstraintsVariableNames.lookup 37 = some "addr ofL (L2)" ∧
    importedConstraintsVariableNames.lookup 38 = some "addr ofH (L2)" ∧
    importedConstraintsVariableNames.lookup 39 = some "cleanaddr_lo (canonical 16-bit)" ∧
    importedConstraintsVariableNames.lookup 40 = some "cleanaddr_lo >> 2 (word cell index low)" ∧
    importedConstraintsVariableNames.lookup 41 = some "flag: are we in rom addr range?" ∧
    importedConstraintsVariableNames.lookup 42 = some "residue (L2)" ∧
    importedConstraintsVariableNames.lookup 43 = some "clear (SB: mem[addr] halfword byte gets set to 0)" ∧
    importedConstraintsVariableNames.lookup 44 = some "STORE*B: clear's table input: SEL(b1, OLDH, OLDL) || b0 (L2)" ∧
    importedConstraintsVariableNames.lookup 45 = some "clear (L2)" ∧
    importedConstraintsVariableNames.lookup 46 = some "rom (L2)" ∧
    importedConstraintsVariableNames.lookup 47 = some "ram (L2)" ∧
    importedConstraintsVariableNames.lookup 48 = some "store (L2)" ∧
    importedConstraintsVariableNames.lookup 49 = some "rom_input (L2)" ∧
    importedConstraintsVariableNames.lookup 50 = some "ram_input (L2)" ∧
    importedConstraintsVariableNames.lookup 51 = some "store_bytemasked_input (L2)" ∧
    importedConstraintsVariableNames.lookup 52 = some "final lookup input (L3)" ∧
    importedConstraintsVariableNames.lookup 53 = some "memwrite_lo (L2)" ∧
    importedConstraintsVariableNames.lookup 54 = some "keep (L2)" ∧
    importedConstraintsVariableNames.lookup 55 = some "final lookup output1 (L3)" ∧
    importedConstraintsVariableNames.lookup 56 = some "memwrite_hi (L2)" ∧
    importedConstraintsVariableNames.lookup 57 = some "constrained_memwrite_halfword (L2)" ∧
    importedConstraintsVariableNames.lookup 58 = some "final lookup output2 (L3)" ∧
    importedConstraintsVariableNames.lookup 59 = some "table_id (L2)" ∧
    importedConstraintsVariableNames.lookup 60 = some "execute (L2)" ∧
    importedConstraintsVariableNames.lookup 61 = some "final lookup table_id (L3)" ∧
    importedConstraintsVariableNames.lookup 62 = some "query 0, interim ts borrow" ∧
    importedConstraintsVariableNames.lookup 63 = some "query 1, interim ts borrow" ∧
    importedConstraintsVariableNames.lookup 64 = some "query 2, interim ts borrow" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.SubwordMemory
