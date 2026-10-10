import Airbender.Proofs.UnifiedReduced.RegisterRetirement
import Airbender.Proofs.UnifiedReduced.StoreRetirement
import Airbender.Proofs.UnifiedReduced.ROMSoundness

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem word_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows)
    {before after : State} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {entry : ProgramEntry}
    (inputs : WordMemory.NativeROM.InterfaceAssumptions trace initial cells program input output w)
    (words : WordMemory.WordMapping input output w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition (ROMView.data initial trace) initial cells ⟨.machine, w⟩ input.before)
    (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have result := WordMemory.NativeROM.Proofs.soundness hp inverse trace initial cells program input output w
    ⟨inputs, ⟨accepted, decoded, member⟩, ⟨words, position, entry, present, query, encoding⟩⟩
  have physical := ROMView.accepted (by omega) initial accepted
  have nativeInputs := ROMView.boot_inputs (by omega) inputs.boot
  obtain ⟨addresses, image⟩ := nativeInputs.programImage
  have fields := (run_program_sources image entry present).fields
  have metadata := WordMemory.Proofs.decoded_metadata fields encoding inputs.destination
  have core := Verification.holds_of_sublist (physical.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints trace.rom) at core
  have outputData : output.data = Control.destination w := congrArg₂ Word.mk words.dataLo words.dataHi
  have outputPC : output.pc = Control.finalPC w := congrArg₂ Word.mk words.finalPCLo words.finalPCHi
  refine ⟨Airbender.WordMemory.execution input, ?_, ?_⟩
  · rw [encoding]; cases mode : input.store <;> simp [Airbender.WordMemory.execution, mode, instructionClause]
  · cases mode : input.store
    · have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
          (Airbender.WordMemory.execution input) input.rd ⟨Control.destination w, Control.finalPC w⟩ := by
        simpa only [Airbender.WordMemory.spec, mode, Bool.false_eq_true, if_false,
          atRow, outputData, outputPC] using result.2
      have index : entry.data.rd = match input.rd with | .Regidx bits => bits := by
        rw [metadata]; simp [WordMemory.Proofs.metadata, mode]
      have mask : entry.data.mask < 262144 := by rw [metadata]; simp [WordMemory.Proofs.metadata, mode]
      exact register_retirement (by omega) core fields query mask index trace.memoryEpoch history spec
    · have flags := decoder_selectors (by omega) core (decoder_field_bounds fields).2.1 query
      have store : w 29 = 1 := by
        have bit := flags 18
        rw [metadata] at bit
        simpa [WordMemory.Proofs.metadata, mode, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
      have address : output.address = Word.mk (w 44).val (w 45).val := by
        apply congrArg₂ Word.mk
        · simpa [mode] using words.addressLo
        · simpa [mode] using words.addressHi
      have addressBound : (Word.mk (w 44).val (w 45).val).Bounded := by
        constructor
        · simpa [Expression.eval, Verification.environment] using
            Verification.range16_bound (Verification.lookup_of_holds core ⟨8, by rw [lookup_count]; decide⟩)
        · simpa [Expression.eval, Verification.environment] using
            Verification.range16_bound (Verification.lookup_of_holds core ⟨9, by rw [lookup_count]; decide⟩)
      have spec : stepSpec (retiredState before (Control.initialPC w).toBitVec)
          (Airbender.WordMemory.execution input) zeroRegister ⟨⟨0, 0⟩, Control.finalPC w⟩
          (writeMemory (size := 4) (Word.mk (w 44).val (w 45).val).toBitVec (Control.destination w).toBitVec) := by
        simpa only [mode, if_true, atRow, address, outputData, outputPC] using result.2
      obtain ⟨written, normal, projected⟩ := spec
      have effects := store_effects store addressBound trace.memoryEpoch history
      have same := (EStateM.Result.ok.inj (projected.symm.trans effects)).2
      simpa only [same] using normal

end Airbender.UnifiedReduced.Proofs
