module
public import Proven.Blake2Round.Mask.RVReference
public import Proven.Blake2Round.Mask.RVBodies

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Specs.BLAKE3.g Specs.BLAKE3.round

/-- Native observable outputs form the exact pure RV mask effect on the observed source blocks. -/
theorem masked_body {input : Input} {output : Output} (mem : RV.Word → BitVec 8) (state message : RV.Word)
    (assumptions : Assumptions input) (correct : spec input output)
    (stateRead : input.state.map Word.toBitVec = RV.readWords mem state 8)
    (extendedRead : input.extended.map Word.toBitVec = RV.readWords mem (state + 32) 16)
    (messageRead : input.message.map Word.toBitVec = RV.readWords mem message 16)
    (mask : ∀ r : Fin 10, RV.Delegation.roundMaskBit input.controller.toBitVec r = input.rounds r)
    (modes : input.controller.toBitVec.getLsbD 16 = input.reducedRounds ∧
      input.controller.toBitVec.getLsbD 17 = input.inputIsRight ∧
      input.controller.toBitVec.getLsbD 18 = input.compression) :
    RV.Delegation.blakeRoundMasked state message input.controller.toBitVec mem =
      (⟨RV.writesAt state (output.state.map Word.toBitVec) ++
        RV.writesAt (state + 32) (output.extended.map Word.toBitVec), 12,
        output.controller.toBitVec⟩ : RV.Effect) := by
  have mixed := mixing_reference assumptions correct mask
  have final := finalization_reference correct
  have next := (congrArg Word.toBitVec correct.1.2).trans (next_bits input.controller assumptions.controller)
  have finalFlag : RV.Delegation.maskedRoundFinal input.controller.toBitVec = isFinal input := by
    rw [RV.Delegation.maskedRoundFinal, mask 6, mask 9, modes.1]
    rfl
  have working : maskedMixed input.controller.toBitVec (input.state.map Word.toBitVec)
      (input.extended.map Word.toBitVec) (input.message.map Word.toBitVec) = output.extended.map Word.toBitVec := by
    rw [maskedMixed, maskedMessage, maskedPrepared, modes.2.1, modes.2.2, mask 0]
    exact mixed.symm
  rw [masked_reads, ← stateRead, ← extendedRead, ← messageRead, maskedBody, working,
    finalFlag, modes.2.2, ← final, ← next]

end Airbender.Blake2Round.Mask.Proofs
