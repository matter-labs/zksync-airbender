module
public import Proven.Blake2Round.Mask.RVWords

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Specs.BLAKE3.g Specs.BLAKE3.round

/-- A valid one-hot mask has exactly its selected round bit. -/
theorem onehot_mask_bits {control : RV.Word} {r : Nat} (_bound : r < 10)
    (mask : control >>> 19 = 1#32 <<< r) (i : Fin 10) :
    RV.Delegation.roundMaskBit control i = decide (i.val = r) := by
  have one (j : Nat) : (1#32).getLsbD j = decide (j = 0) := by
    change Nat.testBit (Bool.toNat true) j = _
    rw [Nat.testBit_bool_toNat, Bool.and_true]
  rw [RV.Delegation.roundMaskBit, ← BitVec.getLsbD_ushiftRight, mask,
    BitVec.getLsbD_shiftLeft, one]
  have index : i.val < 32 := by have := i.isLt; omega
  simp only [index, decide_true, Bool.true_and]
  by_cases lower : i.val < r
  · have different : i.val ≠ r := by omega
    simp [lower, different]
  · simp only [lower, decide_false, Bool.not_false, Bool.true_and]
    by_cases same : i.val = r
    · simp [same]
    · have different : i.val - r ≠ 0 := by omega
      simp [same, different]

/-- A valid one-hot mask selects precisely one SIGMA-permuted message vector. -/
theorem onehot_message {control : RV.Word} {r : Nat} (bound : r < 10)
    (mask : control >>> 19 = 1#32 <<< r) (message : Vector RV.Word 16) :
    RV.Delegation.maskedRoundMessage control message = Vector.ofFn fun i => message[Spec.SIGMA ⟨r, bound⟩ i] := by
  have contribution (position : Fin 16) :
      ((List.finRange 10).map fun i => if RV.Delegation.roundMaskBit control i
        then message[Spec.SIGMA i position].toNat else 0).sum =
        message[Spec.SIGMA ⟨r, bound⟩ position].toNat := by
    rw [ten_sum]
    have selected (i : Fin 10) :
        (if RV.Delegation.roundMaskBit control i then message[Spec.SIGMA i position].toNat else 0) =
          if i = ⟨r, bound⟩ then message[Spec.SIGMA ⟨r, bound⟩ position].toNat else 0 := by
      rw [onehot_mask_bits bound mask]
      by_cases same : i = ⟨r, bound⟩
      · subst same
        simp
      · have different : i.val ≠ r := fun equal => same (Fin.ext equal)
        simp [same, different]
    rw [Finset.sum_congr rfl (fun i _ => selected i)]
    simp
  apply Vector.ext
  intro i size
  simp only [RV.Delegation.maskedRoundMessage, Vector.getElem_ofFn]
  rw [contribution]
  simp

/-- A one-hot masked round is the ordinary SIGMA round. -/
theorem onehot_round {control : RV.Word} {r : Nat} (bound : r < 10)
    (mask : control >>> 19 = 1#32 <<< r) (message state : Vector RV.Word 16) :
    Spec.round (RV.Delegation.maskedRoundMessage control message) id state =
      Spec.round message (Spec.SIGMA ⟨r, bound⟩) state := by
  rw [onehot_message bound mask]
  simp only [Spec.round, Fin.getElem_fin, Vector.getElem_ofFn, id_eq]

/-- The native finalization selector agrees with the valid one-hot schedule. -/
theorem onehot_final {control : RV.Word} {r : Nat}
    (bound : r < if control.getLsbD 16 then 7 else 10)
    (mask : control >>> 19 = 1#32 <<< r) :
    RV.Delegation.maskedRoundFinal control = decide (r + 1 = if control.getLsbD 16 then 7 else 10) := by
  have small : r < 10 := by split at bound <;> omega
  have valid : ∀ reduced : Bool, ∀ index : Fin 10,
      index.val < (if reduced then 7 else 10) →
      (if decide (6 = index.val) then reduced else decide (9 = index.val)) =
        decide (index.val + 1 = if reduced then 7 else 10) := by decide +kernel
  rw [RV.Delegation.maskedRoundFinal, onehot_mask_bits small mask 6, onehot_mask_bits small mask 9]
  exact valid (control.getLsbD 16) ⟨r, small⟩ bound

end Airbender.Blake2Round.Mask.Proofs
