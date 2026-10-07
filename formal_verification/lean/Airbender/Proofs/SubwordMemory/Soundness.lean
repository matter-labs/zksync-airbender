import Airbender.Review.SubwordMemory.Model
import Airbender.Proofs.SubwordMemory.Data

namespace Airbender.SubwordMemory.Proofs
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem

variable [MemoryPlatform SailRV32.exception]

theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (program : Nat → BitVec 32) :
    (circuitModel (p := p) program).SoundnessUnder InterfaceAssumptions spec := by
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
  have address := effective_address hp inverse false h interface.load
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
  have classified := rom_selection (by omega : 131072 < p) false h interface.load mapping.cellHi address.1
  have ram : w 41 = 0 := by
    simpa [show ¬ output.cell.hi < 64 by have outside := interface.ramAddress; omega] using classified.1
  have data := ram_load_data hp input.byte input.signed highByte highHalf h
    interface.active interface.load ram interface.byteSelection interface.signedSelection bit0 bit1
    ⟨mapping.readLo, mapping.readHi⟩ interface.readDataBound halfAligned
  rw [← mapping.outputLo, ← mapping.outputHi] at data
  have read := interface.loadRead
  rw [← cellCorrect, cellNat] at read
  have offsetBound : offset < 4 := address.2.2.1
  have even : input.byte = false → offset % 2 = 0 := by
    intro half
    have low := halfAligned half
    cases eq : highHalf <;> simp [offset, low, eq]
  have bytes := Sail.read_subword input.byte offsetBound even read
  rw [← naturalAddress] at bytes
  have pc := pc_successor (by omega : 196608 < p) inverse h
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ interface.initialPCBound
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have sourceRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.sourceRead
  have access := interface.memory output.pc.toBitVec _ sourceRead bytes
  rw [interface.signExtension] at access
  have executed := Sail.load (rd := input.rd)
    (by cases input.byte <;> decide) (!input.signed) access
  rw [← data.2] at executed
  refine ⟨cellCorrect, ?_⟩
  apply Sail.retire_of_destination interface.pcRead pc.2.2
  obtain ⟨written, writeRun, _⟩ := Sail.gpr_write_nextPC input.rd output.data.toBitVec prepared
  have resultRun : run (Sail.writeResult input.rd output.data) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS written := by
    simp only [Sail.writeResult]
    rw [run_bind_of_ok _ _ _ _ _ writeRun]
    rfl
  refine ⟨written, ?_, resultRun⟩
  simpa only [execution, Sail.writeResult] using
    executed.trans (by simpa only [Sail.writeResult] using resultRun)

end Airbender.SubwordMemory.Proofs
