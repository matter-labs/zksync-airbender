import Airbender.Proofs.Trace.Families.WordMemory.ROMTransport

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
/-- Original ROM loads write the unmasked ROM word in Sail. The native masked
    final port is the same effect: nonzero rd receives both actual ROM limbs,
    while original x0 writes discard either value. No NOP projection is used. -/
theorem projected_rom_destination_write {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    (region : (addressWord w).hi < 64) {before after : State}
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Word.mk (w 26).val (w 27).val).toBitVec) before = .ok () after := by
  change (w 20).val < 64 at region
  have effects := transfers hp native
  have load : w 12 = 0 := effects.storeBit.resolve_right (by
    intro store
    have ram := (effects.store store).1
    omega)
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
    rw [Reference.RiscV.Sail.write_zero (Word.mk (w 26).val (w 27).val).toBitVec]
    exact actual
  · have flag := congrArg (fun q : Vector (ZMod p) 10 => q[5]) query
    change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
    rw [if_neg zero] at flag
    have copied := effects.load load
    have words := rom_values hp native
    dsimp only at copied
    simp only [flag, sub_zero, one_mul, if_pos region] at copied
    have lo : w 37 = w 26 := copied.1.trans words.2.1.symm
    have hi : w 38 = w 27 := copied.2.trans words.2.2.symm
    simpa only [lo, hi] using actual

set_option backward.isDefEq.respectTransparency false in
/-- Original decoded LW execution reaches the actual native after-state.
    Public bytes/native ports supply its memory value and actual masked write;
    decoder fields supply original registers and sign-extended immediate. -/
theorem projected_rom_load_execution {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {before after : State} (configuration : FlatMemoryConfiguration before)
    {count : Nat} (image : wordROMImage before count = some rom)
    (region : (addressWord w).hi < 64) (within : (addressWord w).value < 4 * count)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have data : entry.data = ⟨.wordMemory, rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 2⟩ := by
    rw [instruction] at fields
    exact (Option.some.inj fields).symm
  have immediate := Trace.Proofs.native_query_immediate_word
    (by dsimp [limbBase]; omega) (decoder_field_bounds fields).1 query
  change immediateWord w = entry.data.immediate at immediate
  have read := projected_virtual_rom_read hp epoch native address query configuration image region within history
  have written := projected_rom_destination_write hp epoch native query region history
  rw [data] at immediate read written
  rw [immediate, Word.ofBitVec_roundtrip] at read
  rw [load_word (rd := .Regidx rd) read, run_bind_of_ok _ _ _ _ _ written]
  rfl

end Airbender.WordMemory.Proofs
