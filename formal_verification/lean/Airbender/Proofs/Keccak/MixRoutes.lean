import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Keccak.MixDefinitions
import Airbender.Proofs.Keccak.Tags
import Airbender.Proofs.Constraints.Core
import Mathlib.Tactic.LinearCombination

namespace Airbender.Keccak.Proofs.Mix
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem mix_routes {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 7)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (limb : Fin 4) :
    if isRotation second operation then
      w (102 + 24 * operation.val + limb.val) = w (aColumns second)[operation][limb] + 65536 ∧
      w (118 + 24 * operation.val + limb.val) +
        w (110 + 24 * operation.val + (previous limb).val) = w (cColumns second)[operation][limb]
    else
      w (102 + 24 * operation.val + 2 * limb.val) +
        256 * w (103 + 24 * operation.val + 2 * limb.val) = w (aColumns second)[operation][limb] ∧
      w (110 + 24 * operation.val + 2 * limb.val) +
        256 * w (111 + 24 * operation.val + 2 * limb.val) = w (bColumns second)[operation][limb] ∧
      w (118 + 24 * operation.val + 2 * limb.val) +
        256 * w (119 + 24 * operation.val + 2 * limb.val) = w (cColumns second)[operation][limb] := by
  have modes := selected_modes hp h active (mixMode second) selected
  have m0 := modes (0 : Fin 7); have m1 := modes (1 : Fin 7)
  have m2 := modes (2 : Fin 7); have m3 := modes (3 : Fin 7)
  have m4 := modes (4 : Fin 7); have m5 := modes (5 : Fin 7); have m6 := modes (6 : Fin 7)
  have rho : w 67 = 0 := by
    cases second <;> simpa [Variables.modeColumns, mixMode] using m4
  have rotations (i : Fin 5) : w (80 + i.val) = 0 := by
    have equation := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
    fin_cases i <;>
      simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, rho] using equation.symm
  have r0 := rotations (0 : Fin 5); have r1 := rotations (1 : Fin 5)
  have r2 := rotations (2 : Fin 5); have r3 := rotations (3 : Fin 5); have r4 := rotations (4 : Fin 5)
  change w 80 = 0 at r0
  change w 81 = 0 at r1
  change w 82 = 0 at r2
  change w 83 = 0 at r3
  change w 84 = 0 at r4
  have a := Verification.assertion_of_holds h
    ⟨20 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  have b := Verification.assertion_of_holds h
    ⟨21 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  have c := Verification.assertion_of_holds h
    ⟨22 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  cases second <;> fin_cases operation <;> fin_cases limb <;>
    simp [Variables.modeColumns, mixMode] at m0 m1 m2 m3 m4 m5 m6
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, m0, m1, m2, m3, m4, m5, m6,
    r0, r1, r2, r3, r4, aColumns, bColumns, cColumns, nativeLimbs, temporary, isRotation, previous] at a b c ⊢
  all_goals first
    | exact ⟨by linear_combination a, by linear_combination c⟩
    | exact ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩


end Airbender.Keccak.Proofs.Mix
