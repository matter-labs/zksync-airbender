module
public import Proven.Blake2Round.Mask.RVWords
public import Proven.Blake2Round.PreparationBounds

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Specs.BLAKE3.g Specs.BLAKE3.round

/-- Encode a vector of native word values as RV words. -/
theorem encoded_words {n : Nat} (words : Vector Word n) :
    words.map Word.toBitVec = (words.map Word.value).map (BitVec.ofNat 32) := by
  apply Vector.ext
  intro i bound
  simp only [Vector.getElem_map, Word.toBitVec]

/-- Preparation uses the first native mask bit, independently of all later bits. -/
theorem prepared_extended_any (compression right first : Bool) (h : Vector Word 8) (e m : Vector Word 16) :
    (Preparation.step ⟨first, compression, right, h, e, m⟩).extended.map Word.toBitVec =
      if first then RV.bV0 compression (h.map Word.toBitVec) (e.map Word.toBitVec) else e.map Word.toBitVec := by
  cases first
  · rfl
  · cases compression
    · simpa [Preparation.step, RV.bV0] using Blake2Round.Proofs.normal_v0 h e
    · simpa [Preparation.step, RV.bV0] using Blake2Round.Proofs.compression_v0

/-- The pure RV working vector for one native Boolean-mask round. -/
def referenceExtended (input : Input) : Vector RV.Word 16 :=
  Spec.round (RV.Delegation.maskedRoundMessage input.controller.toBitVec
      (RV.bMsg input.inputIsRight input.compression (input.state.map Word.toBitVec) (input.message.map Word.toBitVec)))
    id (if input.rounds 0 then RV.bV0 input.compression (input.state.map Word.toBitVec)
      (input.extended.map Word.toBitVec) else input.extended.map Word.toBitVec)

/-- The native mixing result is the RV round on the complete selected-message sum. -/
theorem mixing_reference {input : Input} {output : Output}
    (assumptions : Assumptions input) (correct : spec input output)
    (mask : ∀ r : Fin 10, RV.Delegation.roundMaskBit input.controller.toBitVec r = input.rounds r) :
    output.extended.map Word.toBitVec = referenceExtended input := by
  let prepared := Preparation.step (preparationInput input)
  have bounds := Preparation.Proofs.output_bounded (input := preparationInput input)
    assumptions.state assumptions.extended assumptions.message
  have source : (prepared.extended.map Word.toBitVec).map BitVec.toNat = prepared.extended.map Word.value := by
    apply Vector.ext
    intro i bound
    simp only [Vector.getElem_map]
    exact Word.toBitVec_toNat (bounds.2.1 ⟨i, bound⟩)
  have selected := scheduled_bits input.rounds prepared.message input.controller.toBitVec bounds.2.2 mask
  have message : (Vector.ofFn fun i =>
      (RV.Delegation.maskedRoundMessage input.controller.toBitVec (prepared.message.map Word.toBitVec))[id i].toNat) =
      ((scheduledMessage input.rounds prepared.message).map Word.value).map (fun word => word % 2 ^ 32) := by
    rw [← selected]
    apply Vector.ext
    intro i bound
    simp only [Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map, id_eq, Word.toBitVec, BitVec.toNat_ofNat]
  have mixed : output.extended.map Word.value =
      Specs.BLAKE3.round (prepared.extended.map Word.value)
        ((scheduledMessage input.rounds prepared.message).map Word.value) := correct.2.1
  have result : output.extended.map Word.toBitVec =
      Spec.round (RV.Delegation.maskedRoundMessage input.controller.toBitVec (prepared.message.map Word.toBitVec))
        id (prepared.extended.map Word.toBitVec) := by
    rw [encoded_words, mixed]
    unfold Spec.round
    rw [source, message, round_message_mod]
  change output.extended.map Word.toBitVec = referenceExtended input
  unfold referenceExtended
  simpa only [prepared, preparationInput, Blake2Round.Proofs.prepared_message, prepared_extended_any] using result

/-- The native finalization result is the RV chaining fold, with bit-six priority. -/
theorem finalization_reference {input : Input} {output : Output} (correct : spec input output) :
    output.state.map Word.toBitVec =
      if isFinal input then RV.blakeFinal (RV.bH0 input.compression (input.state.map Word.toBitVec))
        (output.extended.map Word.toBitVec) else input.state.map Word.toBitVec := by
  have final := correct.2.2.1
  cases last : isFinal input
  · simp only [last, Bool.false_eq_true, ↓reduceIte] at final ⊢
    rw [final]
  · simp only [last, ↓reduceIte] at final ⊢
    rw [encoded_words, final]
    rw [← Blake2Round.Proofs.prepared_chaining input.compression input.inputIsRight (input.rounds 0)
      input.state input.extended input.message]
    apply Vector.ext
    intro i bound
    simp only [Vector.getElem_map, Vector.getElem_ofFn, RV.blakeFinal, Word.toBitVec,
      BitVec.ofNat_xor, Fin.getElem_fin, preparationInput, Nat.add_comm]

end Airbender.Blake2Round.Mask.Proofs
