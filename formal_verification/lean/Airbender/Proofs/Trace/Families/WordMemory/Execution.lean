import Airbender.Proofs.Trace.Families.WordMemory.Retirement
import Airbender.Review.Helpers.Decoder.Instruction

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
/-- Actual public decoding selects original LW/SW. Initialized native history
    derives effective addresses and modular PC successors; the original Sail
    preparation/clause/retirement reaches that same actual cell state and PC.
    Prefix coverage and ordinary RAM addresses remain explicit local domains. -/
theorem indexed_instruction_retirement [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {initial before after : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count romCount : Nat}
    (inputs : ShadowImageBoundary trace initial cells seeds)
    (decoder : IndexedProgram initial count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod mersenne31Modulus}
    (member : (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily) ∈ trace.rows)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily).decoderQuery = entry.query)
    (configuration : FlatMemoryConfiguration before)
    (image : wordROMImage before romCount = some trace.rom)
    (ordinary : 64 ≤ (w 20).val → OrdinaryWordAddress (addressWord w).toBitVec)
    (within : (addressWord w).hi < 64 → (addressWord w).value < 4 * romCount)
    (history : SailHistory cells
      ((rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  have native := accepted.constraints _ member
  have effects := indexed_projected_native_effects inputs decoder accepted decoded _ member
  have next := effects.2.2.2.2.1
  change (Word.mk (w 13).val (w 14).val).toBitVec =
    (Word.mk (w 0).val (w 1).val).toBitVec + 4 at next
  rw [next]
  have original := fields
  unfold decoderFields at fields
  split at fields
  case h_1 =>
    rename_i _ imm rs1 rd instruction
    refine ⟨SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4, ?_, ?_⟩
    · rw [instruction]; rfl
    · by_cases region : (addressWord w).hi < 64
      · exact projected_rom_load_retirement (by decide) _ native effects.1 original query instruction
          configuration image region (within region) history _
      · have ram : 64 ≤ (w 20).val := Nat.le_of_not_lt region
        exact projected_ram_load_retirement (by decide) _ native effects.1 original query instruction
          configuration ram (ordinary ram) history _
  case h_2 =>
    rename_i _ imm rs2 rs1 instruction
    refine ⟨SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4, ?_, ?_⟩
    · rw [instruction]; rfl
    · have data : entry.data = ⟨.wordMemory, rs1, rs2, 0,
          Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1, 2⟩ :=
        (Option.some.inj fields).symm
      have store : w 12 = 1 := by
        have selected := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
        change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at selected
        rw [data] at selected
        simpa only [Nat.cast_one] using selected
      exact projected_ram_store_retirement (by decide) _ native effects.1 original query instruction
        configuration (ordinary ((transfers (by decide) native).store store).1) history _
  case h_3 => cases fields

/-- Preserve the strict constructor interface while sharing clause assembly. -/
theorem initialized_instruction_retirement [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {initial before after : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity romCount : Nat}
    (inputs : ShadowImageBoundary trace initial cells seeds)
    (decoder : decoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod mersenne31Modulus}
    (member : (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily) ∈ trace.rows)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily).decoderQuery = entry.query)
    (configuration : FlatMemoryConfiguration before)
    (image : wordROMImage before romCount = some trace.rom)
    (ordinary : 64 ≤ (w 20).val → OrdinaryWordAddress (addressWord w).toBitVec)
    (within : (addressWord w).hi < 64 → (addressWord w).value < 4 * romCount)
    (history : SailHistory cells
      ((rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row mersenne31Modulus WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) :=
  indexed_instruction_retirement inputs (strict_indexed_program decoder) accepted decoded
    member fields query configuration image ordinary within history

end Airbender.WordMemory.Proofs
