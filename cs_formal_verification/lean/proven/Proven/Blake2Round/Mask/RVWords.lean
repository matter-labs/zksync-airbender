module
public import Proven.Blake2Round.RVSpec
public import Human.Circuits.Blake2Round.Mask

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
set_option warningAsError true
open Arithmetic
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Reducing either message word modulo 32 bits does not change a G operation. -/
theorem g_message_mod (state : Vector Nat 16) (a b c d : Fin 16) (mx my : Nat) :
    Specs.BLAKE3.g state a b c d (mx % 2 ^ 32) (my % 2 ^ 32) =
      Specs.BLAKE3.g state a b c d mx my := by
  simp only [Specs.BLAKE3.g, add32, Nat.add_mod_mod]

/-- A round depends on the message words only modulo 32 bits. -/
theorem round_message_mod (state message : Vector Nat 16) :
    Specs.BLAKE3.round state (message.map fun word => word % 2 ^ 32) =
      Specs.BLAKE3.round state message := by
  have transition :
      (fun (current : Vector Nat 16) (indices : Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16) =>
        Specs.BLAKE3.g current indices.1 indices.2.1 indices.2.2.1 indices.2.2.2.1
          (message.map fun word => word % 2 ^ 32)[indices.2.2.2.2.1]
          (message.map fun word => word % 2 ^ 32)[indices.2.2.2.2.2]) =
      (fun current indices => Specs.BLAKE3.g current indices.1 indices.2.1 indices.2.2.1 indices.2.2.2.1
          message[indices.2.2.2.2.1] message[indices.2.2.2.2.2]) := by
    funext current indices
    simp only [Fin.getElem_fin, Vector.getElem_map]
    exact g_message_mod current _ _ _ _ _ _
  unfold Specs.BLAKE3.round
  rw [transition]

/-- The list and finite-sum forms of the ten mask contributions agree. -/
theorem ten_sum (f : Fin 10 → Nat) : ((List.finRange 10).map f).sum = ∑ r : Fin 10, f r := by
  simp only [show List.finRange 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

/-- Native limb sums are the sum of the selected complete word values. -/
theorem scheduled_value (rounds : Fin 10 → Bool) (message : Vector Word 16) (position : Fin 16) :
    (scheduledMessage rounds message)[position].value =
      ∑ r : Fin 10, if rounds r then message[Spec.SIGMA r position].value else 0 := by
  simp only [scheduledMessage, Fin.getElem_fin, Vector.getElem_ofFn, Word.value]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have words := congrArg (fun index : Fin 16 => message[index])
    (Blake2Round.Proofs.schedule_sigma r position)
  cases selected : rounds r
  · simp
  · simpa only [selected, ↓reduceIte, Word.value, Fin.getElem_fin] using congrArg Word.value words

/-- The native scheduled words encode the RV arbitrary-mask message. -/
theorem scheduled_bits (rounds : Fin 10 → Bool) (message : Vector Word 16) (control : RV.Word)
    (bounded : ∀ i : Fin 16, message[i].Bounded)
    (mask : ∀ r : Fin 10, RV.Delegation.roundMaskBit control r = rounds r) :
    (scheduledMessage rounds message).map Word.toBitVec =
      RV.Delegation.maskedRoundMessage control (message.map Word.toBitVec) := by
  apply Vector.ext
  intro i bound
  simp only [RV.Delegation.maskedRoundMessage, Vector.getElem_map, Vector.getElem_ofFn]
  change BitVec.ofNat 32 ((scheduledMessage rounds message)[i].value) = _
  have values := scheduled_value rounds message ⟨i, bound⟩
  simp only [Fin.getElem_fin] at values
  rw [values, ten_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [mask r]
  cases rounds r
  · rfl
  · simp only [↓reduceIte, Fin.getElem_fin, Vector.getElem_map]
    simpa only [Fin.getElem_fin] using
      (Word.toBitVec_toNat (bounded (Spec.SIGMA r ⟨i, bound⟩))).symm

end Airbender.Blake2Round.Mask.Proofs
