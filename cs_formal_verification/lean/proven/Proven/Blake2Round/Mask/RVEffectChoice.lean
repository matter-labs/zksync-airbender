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
  by_cases valid : RV.Delegation.blakeRoundPointers state message ∧
      control >>> 19 = 1#32 <<< r ∧ r < (if control.getLsbD 16 then 7 else 10)
  · rw [ite_eq_left valid, scheduled_reads]
    exact congrArg some (onehot_body state valid.2.2 valid.2.1 _ _ _).symm
  · rw [ite_eq_right valid]
    have pointers : RV.Delegation.blakeRoundPointers state message :=
      ⟨stateAligned, messageFits, messageAligned, separate⟩
    rw [ite_eq_left ⟨pointers, controlBound⟩, masked_reads]

/-- A one-hot native mask has the public reference-round effect. -/
theorem onehot_reference : RV.Delegation.BlakeRoundOneHotClaim := by
  intro state message control mem r bound mask
  rw [masked_reads, scheduled_reads]
  exact onehot_body state bound mask _ _ _

/-- Round zero has a valid one-hot control word. -/
theorem onehot_reference_satisfiable : RV.Delegation.BlakeRoundOneHotSatisfiableClaim := by
  exact ⟨0#32, 64#32, 0x80000#32, fun _ => 0, 0, by decide, by decide⟩

end Airbender.Blake2Round.Mask.Proofs
