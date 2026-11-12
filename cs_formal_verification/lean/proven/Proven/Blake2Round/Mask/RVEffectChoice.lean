module
public import Proven.Blake2Round.Mask.OneHotBody

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Airbender.Specs.BLAKE3.g Airbender.Specs.BLAKE3.round

/-- Both RV round branches implement the native mask effect on the accepted pointer and control domain. -/
theorem native_round_effect (state message control : RV.Word) (mem : RV.Word → BitVec 8)
    (stateAligned : state.toNat % 128 = 0) (messageAligned : message.toNat % 64 = 0)
    (messageFits : message.toNat + 64 ≤ RV.RAM_END) (separate : state ≠ message)
    (controlBound : control.toNat < 2 ^ 29) :
    RV.Delegation.blakeRound state message control mem = some (RV.Delegation.blakeRoundMasked state message control mem) := by
  rw [masked_reads]
  let r := (control >>> 19).toNat.log2
  dsimp only [RV.Delegation.blakeRound]
  by_cases valid : state.toNat % 128 = 0 ∧ message.toNat + 64 ≤ RV.RAM_END ∧
      message.toNat % 64 = 0 ∧ state ≠ message ∧ control >>> 19 = 1#32 <<< r ∧
      r < (if control.getLsbD 16 then 7 else 10)
  · rw [ite_eq_left valid]
    obtain ⟨_, _, _, _, mask, bound⟩ := valid
    rw [onehot_body state bound mask]
    dsimp only [scheduledBody, scheduledMixed, maskedMessage, r]
    by_cases zero : (control >>> 19).toNat.log2 = 0
    · simp only [zero, ne_eq, not_true_eq_false, ↓reduceIte]
      rfl
    · simp only [zero, ne_eq, not_false_eq_true, ↓reduceIte]
      rfl
  · rw [ite_eq_right valid]
    simp only [stateAligned, messageAligned, messageFits, separate, controlBound,
      ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    exact congrArg some (masked_reads state message control mem)

end Airbender.Blake2Round.Mask.Proofs
