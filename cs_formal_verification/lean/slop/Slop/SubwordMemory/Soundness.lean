import Slop.SubwordMemory.RowModel
import Slop.SubwordMemory.Data
import Slop.SubwordMemory.Stores

namespace Airbender.SubwordMemory.Proofs
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem

variable [MemoryPlatform SailRV32.exception]

theorem soundness {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (program : Nat → BitVec 32) :
    (rowCircuitModel (p := p) program).SoundnessUnder (RowInterfaces program) spec := by
  intro input output w ⟨interface, h, mapping⟩
  let highByte := decide (w 35 = 1)
  let highHalf := decide (w 36 = 1)
  have bit0 : w 35 = if highByte then 1 else 0 := by
    have flag : w 35 = 0 ∨ w 35 = 1 := local_flags h 4
    rcases flag with zero | one
    · simp [highByte, zero]
    · simp [highByte, one]
  have bit1 : w 36 = if highHalf then 1 else 0 := by
    have flag : w 36 = 0 ∨ w 36 = 1 := local_flags h 5
    rcases flag with zero | one
    · simp [highHalf, zero]
    · simp [highHalf, one]
  have oneVal : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (show 1 < p by omega))
  have lowVal : (w 35).val = (if highByte then 1 else 0) := by rw [bit0]; cases highByte <;> simp [oneVal]
  have highVal : (w 36).val = (if highHalf then 1 else 0) := by rw [bit1]; cases highHalf <;> simp [oneVal]
  have halfAligned : input.byte = false → highByte = false := by
    intro half
    have selected : w 11 = 0 := by simpa [half] using interface.byteSelection
    have zero := halfword_aligned h selected
    have natural : (w 35).val = 0 := by rw [zero]; simp
    rw [lowVal] at natural
    cases eq : highByte <;> simp [eq] at natural ⊢
  let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
  have address := effective_address (by omega : 262144 < p) inverse input.store h interface.selected
    ⟨mapping.sourceLo, mapping.sourceHi, mapping.immediateLo, mapping.immediateHi,
      mapping.cellLo, mapping.cellHi⟩
    interface.sourceBound interface.immediateBound interface.cellHighBound
  simp only [lowVal, highVal] at address
  have cellNat := Word.toBitVec_toNat address.1
  have noWrap : output.cell.value + offset < 4294967296 := by
    have small := Word.value_lt address.1
    unfold wordModulus at small
    have aligned := address.2.1
    have offsetBound := address.2.2.1
    change offset < 4 at offsetBound
    omega
  have naturalAddress : (input.source.toBitVec + input.immediate.toBitVec).toNat =
      output.cell.value + offset := by
    rw [← address.2.2.2.1]
    simp only [BitVec.toNat_add, cellNat, BitVec.toNat_ofNat]
    norm_num only [Nat.reducePow]
    have offsetBound := address.2.2.1
    change offset < 4 at offsetBound
    omega
  have cellCorrect : output.cell.toBitVec.toNat =
      (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 := by
    rw [cellNat, naturalAddress]
    have aligned := address.2.1
    have offsetBound := address.2.2.1
    change offset < 4 at offsetBound
    omega
  have classified := rom_selection (by omega : 131072 < p) input.store h interface.selected mapping.cellHi address.1
  have pc := pc_successor (by omega : 196608 < p) inverse h
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ interface.initialPCBound
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have sourceRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.sourceRead
  have offsetBound : offset < 4 := address.2.2.1
  have even : input.byte = false → offset % 2 = 0 := by
    intro half
    have low := halfAligned half
    cases eq : highHalf <;> simp [offset, low, eq]
  refine ⟨cellCorrect, ?_⟩
  cases mode : input.store
  · simp only [Bool.false_eq_true, ite_false]
    have load : w 10 = 0 := by simpa [mode] using interface.selected
    let nativeWord := if output.cell.hi < 64 then program (output.cell.value / 4) else input.readData.toBitVec
    have loaded : readBytes (ue := SailRV32.exception) 4 output.cell.value input.before =
        .ok nativeWord input.before ∧ output.data.toBitVec = SailRV32.Functions.extend_value (!input.signed)
          ((nativeWord >>> (8 * offset)).setWidth (8 * (if input.byte then 1 else 2))) := by
      by_cases inROM : output.cell.hi < 64
      · have rom : w 41 = 1 := by simpa [inROM] using classified.1
        have cellMapping : output.cell.lo = (w 21).val ∧ w 22 = (output.cell.hi : ZMod p) := by
          simpa [mode] using And.intro mapping.cellLo mapping.cellHi
        have data := rom_load_data hp input.byte input.signed highByte highHalf h
          interface.active load rom interface.byteSelection interface.signedSelection bit0 bit1
          cellMapping address.1 inROM halfAligned
        rw [← mapping.outputLo, ← mapping.outputHi] at data
        have read := interface.romImage mode inROM
        rw [cellNat] at read
        simpa only [nativeWord, inROM, ite_true] using And.intro read data.2
      · have outside : 64 ≤ output.cell.hi := by omega
        have ram : w 41 = 0 := by simpa [inROM] using classified.1
        have data := ram_load_data (by omega : 262144 < p) input.byte input.signed highByte highHalf h
          interface.active load ram interface.byteSelection interface.signedSelection bit0 bit1
          ⟨mapping.readLo, mapping.readHi⟩ (interface.readDataBound outside) halfAligned
        rw [← mapping.outputLo, ← mapping.outputHi] at data
        have read := interface.loadRead mode outside
        rw [← cellCorrect, cellNat] at read
        simpa only [nativeWord, inROM, ite_false] using And.intro read data.2
    have bytes := Sail.read_subword input.byte offsetBound even loaded.1
    rw [← naturalAddress] at bytes
    have access := interface.memory.load mode output.pc.toBitVec _ sourceRead bytes
    rw [interface.signExtension] at access
    have executed := Sail.load (rd := input.rd)
      (by cases input.byte <;> decide) (!input.signed) access
    rw [← loaded.2] at executed
    apply Sail.retire_of_destination interface.pcRead pc.2.2
    obtain ⟨written, writeRun, _⟩ := Sail.gpr_write_nextPC input.rd output.data.toBitVec prepared
    have resultRun : run (Sail.writeResult input.rd output.data) prepared =
        .ok SailRV32.Functions.RETIRE_SUCCESS written := by
      simp only [Sail.writeResult]
      rw [run_bind_of_ok _ _ _ _ _ writeRun]
      rfl
    refine ⟨written, ?_, resultRun⟩
    cases hb : input.byte <;>
      simpa [execution, instruction, Trace.instructionClause, mode, hb, Sail.writeResult] using
        executed.trans (by simpa only [Sail.writeResult] using resultRun)
  · simp only [ite_true]
    have store : w 10 = 1 := by simpa [mode] using interface.selected
    have dataMapping := And.intro mapping.readLo (And.intro (mapping.oldLo mode) (mapping.oldHi mode))
    have outside := classified.2 mode
    have ram : w 41 = 0 := by simpa [show ¬ output.cell.hi < 64 by omega] using classified.1
    have encoded := store_byte_encoding (by omega : 262144 < p) input.byte highByte highHalf h
      interface.active store ram interface.byteSelection bit0 bit1 dataMapping
      (interface.readDataBound outside) (interface.oldDataBound mode) halfAligned
    rw [← mapping.outputLo, ← mapping.outputHi] at encoded
    have read := interface.oldRead mode
    rw [← cellCorrect, cellNat] at read
    have oldBytes := Sail.read_word_memory read
    have preparedBytes : ∀ i : Fin 4, prepared.mem[output.cell.toBitVec.toNat + i.val]? =
        some (input.oldData.toBitVec.extractLsb' (8 * i.val) 8) := by
      simpa only [prepared, cellNat] using oldBytes
    have writes := Sail.write_subword_memory (before := prepared) output.cell.toBitVec
      input.oldData.toBitVec output.data.toBitVec input.byte offset offsetBound even
      (by rwa [cellNat]) (input.readData.toBitVec.setWidth (8 * (if input.byte then 1 else 2)))
      preparedBytes encoded
    rw [address.2.2.2.1] at writes
    obtain ⟨written, memoryRun, registers⟩ :=
      Sail.write_word_frame output.cell.toBitVec output.data.toBitVec prepared
    have nativeWrite := writes.symm.trans memoryRun
    have access := interface.memory.store mode output.pc.toBitVec
      (input.readData.toBitVec.setWidth (8 * (if input.byte then 1 else 2))) sourceRead
    rw [run_bind_of_ok _ _ _ _ _ nativeWrite] at access
    change run (SailRV32.Functions.vmem_write input.rs1 input.immediate.toBitVec
      (if input.byte then 1 else 2) (input.readData.toBitVec.setWidth (8 * (if input.byte then 1 else 2)))
      (.Store .Data) false false false) prepared = .ok (.Ok true) written at access
    rw [interface.signExtension] at access
    have executed := Sail.store_subword input.byte
      (Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs2 (interface.storeRead mode)) access
    apply Sail.retire_with_memory interface.pcRead
    refine ⟨written, ?_, ?_, ?_⟩
    · cases hb : input.byte <;>
        simpa [execution, instruction, Trace.instructionClause, mode, hb, pc.2.2] using executed
    · simp only [Sail.writeResult, Sail.write_zero, freeM_pure_bind]
      rw [run_bind_of_ok _ _ _ _ _ memoryRun]
      rfl
    · rw [registers]
      simp [prepared]

end Airbender.SubwordMemory.Proofs
