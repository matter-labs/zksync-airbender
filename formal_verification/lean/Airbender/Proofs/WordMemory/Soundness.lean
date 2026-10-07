import Airbender.Review.WordMemory.Model
import Airbender.Proofs.WordMemory
import Airbender.Proofs.Sail.Memory

namespace Airbender.WordMemory.Proofs
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem

variable [MemoryPlatform SailRV32.exception]

theorem soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (rom : Table (ZMod p) (fields 9)) :
    (circuitModel rom).SoundnessUnder (InterfaceAssumptions rom) spec := by
  intro input output w ⟨interface, h, mapping⟩
  have address := effective_address hp inverse input.store h interface.selected
    ⟨mapping.sourceLo, mapping.sourceHi, mapping.immediateLo, mapping.immediateHi,
      mapping.addressLo, mapping.addressHi⟩
    interface.sourceBound interface.immediateBound interface.addressBound
  have pc := pc_successor hp inverse h
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ interface.initialPCBound
  have classified := rom_selection (by omega) input.store h interface.selected
    mapping.addressHi interface.addressBound
  have data (outside : 64 ≤ output.address.hi) : output.data.toBitVec = input.readData.toBitVec := by
    have ram : w 35 = 0 := by
      simpa [show ¬ output.address.hi < 64 by omega] using classified.1
    have copied := ram_data interface.disabledROM input.store h interface.selected ram
    have bound := interface.readDataBound outside
    have lo : output.data.lo = input.readData.lo := by
      rw [mapping.outputLo, copied.1, mapping.readLo, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by have hb := bound.1; unfold limbBase at hb; omega)
    have hi : output.data.hi = input.readData.hi := by
      rw [mapping.outputHi, copied.2, mapping.readHi, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by have hb := bound.2; unfold limbBase at hb; omega)
    simp only [Word.toBitVec, Word.value, lo, hi]
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have sourceRead := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.sourceRead
  refine ⟨address, ?_⟩
  cases mode : input.store
  · simp only [Bool.false_eq_true, if_false]
    apply Sail.retire_of_destination interface.pcRead pc.2.2
    have bytes : readBytes (ue := SailRV32.exception) 4
        (input.source.toBitVec + input.immediate.toBitVec).toNat input.before =
          .ok output.data.toBitVec input.before := by
      by_cases inROM : output.address.hi < 64
      · have flag : w 35 = 1 := by simpa [inROM] using classified.1
        have query := rom_data h (by simpa [mode] using interface.selected) interface.active flag
        have low : w 19 = (output.address.lo : ZMod p) := by simpa [mode] using mapping.addressLo
        have high : w 20 = (output.address.hi : ZMod p) := by simpa [mode] using mapping.addressHi
        rw [low, high] at query
        have bound := interface.romImage output.address (w 31) (w 32) interface.addressBound inROM query
        rw [address] at bound
        simpa only [Word.toBitVec, Word.value, mapping.outputLo, mapping.outputHi] using bound
      · have outside : 64 ≤ output.address.hi := by omega
        rw [data outside]
        exact interface.loadRead mode outside
    have access := interface.memory.load mode output.pc.toBitVec _ sourceRead bytes
    rw [interface.signExtension] at access
    have executed := Sail.load_word (rd := input.rd) access
    obtain ⟨written, writeRun, _⟩ := Sail.gpr_write_nextPC input.rd output.data.toBitVec prepared
    have resultRun : run (Sail.writeResult input.rd output.data) prepared =
        .ok SailRV32.Functions.RETIRE_SUCCESS written := by
      simp only [Sail.writeResult]
      rw [run_bind_of_ok _ _ _ _ _ writeRun]
      rfl
    refine ⟨written, ?_, resultRun⟩
    simpa only [execution, mode, Bool.false_eq_true, if_false, Sail.writeResult]
      using executed.trans (by simpa only [Sail.writeResult] using resultRun)
  · have copiedData := data (classified.2 mode)
    simp only [if_true]
    apply Sail.retire_with_memory interface.pcRead
    obtain ⟨written, memoryRun, registers⟩ :=
      Sail.write_word_frame output.address.toBitVec input.readData.toBitVec prepared
    have access := interface.memory.store mode output.pc.toBitVec input.readData.toBitVec sourceRead
    rw [← address, run_bind_of_ok _ _ _ _ _ memoryRun] at access
    change run (SailRV32.Functions.vmem_write input.rs1 input.immediate.toBitVec 4
      input.readData.toBitVec (.Store .Data) false false false) prepared = .ok (.Ok true) written at access
    rw [interface.signExtension] at access
    have executed := Sail.store_word (Sail.rX_nextPC (pc := output.pc.toBitVec)
      input.rs2 (interface.storeRead mode)) access
    refine ⟨written, ?_, ?_, ?_⟩
    · simpa only [execution, mode, if_true, pc.2.2] using executed
    · simp only [Sail.writeResult, Sail.write_zero, freeM_pure_bind, copiedData]
      rw [run_bind_of_ok _ _ _ _ _ memoryRun]
      rfl
    · rw [registers]
      simp [prepared]

end Airbender.WordMemory.Proofs
