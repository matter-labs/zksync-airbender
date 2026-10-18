import Airbender.Proofs.Trace.Families.WordMemory.MemoryTransport

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
/-- The actual native masked RAM-load write matches the original Sail write.
    Nonzero rd receives the retained RAM read; x0 discards it without NOP projection. -/
theorem projected_ram_destination_write {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    (load : w 12 = 0) (ram : 64 ≤ (w 20).val) {before after : State}
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Word.mk (w 30).val (w 31).val).toBitVec) before = .ok () after := by
  have effects := transfers hp native
  have space : w 32 = 1 := by simpa only [load, sub_zero] using effects.writeAddress.1
  have low : w 33 = w 7 := by
    simpa only [load, zero_mul, sub_zero, one_mul, zero_add] using effects.writeAddress.2.1
  have high : w 34 = 0 := by simpa only [load, zero_mul] using effects.writeAddress.2.2
  have rd := (Trace.Proofs.native_query_indices (by dsimp [limbBase]; omega) query).2.2
  change (w 7).val = entry.data.rd.toNat at rd
  have address : importedConstraintsMemoryPorts[2].address.code w =
      (Cell.register entry.data.rd).addressCode := by
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, Cell.addressCode,
      space, low, high, rd]
  have written := projected_history_write hp epoch native history
    (port := importedConstraintsMemoryPorts[2]) rfl address
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Word.mk (w 37).val (w 38).val).toBitVec) before = .ok () after := by
    simpa [Cell.write, memoryWord, MemoryPort.writeCode, WordColumns.code,
      WordColumns.evaluate, importedConstraintsMemoryPorts, Nat.unpair_pair] using written
  by_cases zero : entry.data.rd = 0
  · rw [zero] at actual ⊢
    rw [Reference.RiscV.Sail.write_zero (Word.mk (w 37).val (w 38).val).toBitVec] at actual
    rw [Reference.RiscV.Sail.write_zero (Word.mk (w 30).val (w 31).val).toBitVec]
    exact actual
  · have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) query
    change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
    rw [if_neg zero] at flag
    have copied := effects.load load
    dsimp only at copied
    simp only [flag, sub_zero, one_mul, if_neg (Nat.not_lt.mpr ram)] at copied
    simpa only [copied.1, copied.2] using actual

/-- A native store selects rs2 on its retained second port. Its actual read
    is recovered in the instruction pre-state, including source aliases and x0. -/
theorem projected_store_source_read {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) {before after : State}
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after)
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (Word.mk (w 30).val (w 31).val).toBitVec before := by
  have effects := transfers hp native
  have low : w 28 = w 6 := by
    simpa only [store, sub_self, zero_mul, one_mul, zero_add] using effects.readAddress.1
  have high : w 29 = 0 := by simpa only [store, sub_self, zero_mul] using effects.readAddress.2
  have index := (Trace.Proofs.native_query_indices (by dsimp [limbBase]; omega) query).2.1
  change (w 6).val = entry.data.rs2.toNat at index
  have address : importedConstraintsMemoryPorts[1].address.code w =
      (Cell.register entry.data.rs2).addressCode := by
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, Cell.addressCode,
      store, low, high, index]
  have read := projected_history_read hp epoch native history
    (port := importedConstraintsMemoryPorts[1])
    (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    (by rw [address]; exact architectural_register _) address
  simpa [Cell.read, memoryWord, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, Nat.unpair_pair] using read

set_option backward.isDefEq.respectTransparency false in
/-- Original RAM LW reaches the actual native cell-transfer state. The public
    decoder supplies the load selector, original registers and immediate; all
    reads and the unmasked destination effect follow from accepted native ports. -/
theorem projected_ram_load_execution {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (ram : 64 ≤ (w 20).val) (ordinary : OrdinaryWordAddress (addressWord w).toBitVec)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have data : entry.data = ⟨.wordMemory, rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 2⟩ := by
    rw [instruction] at fields
    exact (Option.some.inj fields).symm
  have load : w 12 = 0 := by
    have selected := congrArg (fun q : Vector (ZMod p) 10 => q[9]) query
    change w 12 = (entry.data.mask : ZMod p) at selected
    rw [data] at selected
    simpa only [Nat.cast_zero] using selected
  have immediate := Trace.Proofs.native_query_immediate_word
    (by dsimp [limbBase]; omega) (decoder_field_bounds fields).1 query
  change immediateWord w = entry.data.immediate at immediate
  have read := projected_virtual_ram_read hp epoch native load ram address query configuration ordinary history
  have written := projected_ram_destination_write hp epoch native query load ram history
  rw [data] at immediate read written
  rw [immediate, Word.ofBitVec_roundtrip] at read
  rw [load_word (rd := .Regidx rd) read, run_bind_of_ok _ _ _ _ _ written]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Original SW reads the derived rs2 value and reaches the actual native RAM
    write state. No operand value, expected write or desired state is supplied. -/
theorem projected_ram_store_execution {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rs2 : BitVec 5}
    (instruction : entry.instruction = .STORE (imm, .Regidx rs2, .Regidx rs1, 4))
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (addressWord w).toBitVec)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have data : entry.data = ⟨.wordMemory, rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1, 2⟩ := by
    rw [instruction] at fields
    exact (Option.some.inj fields).symm
  have store : w 12 = 1 := by
    have selected := congrArg (fun q : Vector (ZMod p) 10 => q[9]) query
    change w 12 = (entry.data.mask : ZMod p) at selected
    rw [data] at selected
    simpa only [Nat.cast_one] using selected
  have immediate := Trace.Proofs.native_query_immediate_word
    (by dsimp [limbBase]; omega) (decoder_field_bounds fields).1 query
  change immediateWord w = entry.data.immediate at immediate
  have read := projected_store_source_read hp epoch native store history query
  have written := projected_virtual_ram_write hp epoch native store address query configuration ordinary history
  rw [data] at immediate read written
  rw [immediate, Word.ofBitVec_roundtrip] at written
  exact store_word read written

end Airbender.WordMemory.Proofs
