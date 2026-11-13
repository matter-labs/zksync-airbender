module
public import Human.Circuits.Blake2Round.Mask
public import Proven.Blake2Round.Finalization

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic

/-- The native selector equation uses bit-six priority for every Boolean mask. -/
theorem finalization_flag {input : Input} {output : Output} {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (mapping : Mapping input output w) : w 152 = if isFinal input then 1 else 0 := by
  have flag := Verification.assertion_of_holds holds ⟨2, by rw [constraint_count]; decide⟩
  op_index at flag
  simp [Expression.eval, Verification.environment] at flag
  have equation : w 152 = w 151 + w 148 * (w 139 - w 151) := by linear_combination -flag
  have bit6 := mapping.rounds 6
  have bit9 := mapping.rounds 9
  change w 148 = (if input.rounds 6 then 1 else 0) at bit6
  change w 151 = (if input.rounds 9 then 1 else 0) at bit9
  rw [equation, bit6, bit9, mapping.reduced]
  unfold isFinal
  cases six : input.rounds 6 <;> cases nine : input.rounds 9 <;> cases reduced : input.reducedRounds <;>
    simp

/-- The existing native XOR and preservation proofs need only the actual finalization flag. -/
theorem finalization_of_flag {w : Nat → ZMod babyBearModulus} (final : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (flag : w 152 = if final then 1 else 0) :
    if final then
      (Preparation.words w Finalization.stateWrites).map Word.value = Vector.ofFn fun i : Fin 8 =>
        (Preparation.words w Variables.chainingInputs)[i].value ^^^
        (Preparation.words w Mixing.extendedWrites)[i.val].value ^^^
        (Preparation.words w Mixing.extendedWrites)[8 + i.val].value
    else Preparation.words w Finalization.stateWrites = Preparation.words w Variables.stateReads := by
  cases final
  · exact Blake2Round.Proofs.chaining_preserved holds flag
  · exact Blake2Round.Proofs.final_xor_writes (by decide) (by decide) holds flag

end Airbender.Blake2Round.Mask.Proofs
