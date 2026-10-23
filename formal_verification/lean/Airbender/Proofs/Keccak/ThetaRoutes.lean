import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Keccak.Theta
import Airbender.Proofs.Keccak.Tags
import Airbender.Proofs.Constraints.Core
import Mathlib.Tactic.LinearCombination

namespace Airbender.Keccak.Proofs.ThetaRoutes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private theorem theta_rotations {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 7)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (theta : w 66 = 1) : ∀ i : Fin 5, w (80 + i.val) = 0 := by
  have modes := selected_modes hp h active (3 : Fin 7) theta
  have rho : w 67 = 0 := by simpa [Variables.modeColumns] using modes (4 : Fin 7)
  intro i
  have flag := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
  fin_cases i <;> simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, rho] using flag.symm

private def limbOffsets : Vector Nat 4 := #v[0, 1, 4, 5]

theorem checked {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 7)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (theta : w 66 = 1) (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + 2 * limb.val) +
      256 * w (103 + 24 * operation.val + 2 * limb.val) =
      w (15 + 8 * operation.val + limbOffsets[limb]) ∧
    w (110 + 24 * operation.val + 2 * limb.val) +
      256 * w (111 + 24 * operation.val + 2 * limb.val) = w (55 + limbOffsets[limb]) ∧
    w (118 + 24 * operation.val + 2 * limb.val) +
      256 * w (119 + 24 * operation.val + 2 * limb.val) =
      w (17 + 8 * operation.val + limbOffsets[limb]) := by
  have modes := selected_modes hp h active (3 : Fin 7) theta
  have m0 : w 63 = 0 := by simpa [Variables.modeColumns] using modes (0 : Fin 7)
  have m1 : w 64 = 0 := by simpa [Variables.modeColumns] using modes (1 : Fin 7)
  have m2 : w 65 = 0 := by simpa [Variables.modeColumns] using modes (2 : Fin 7)
  have m4 : w 67 = 0 := by simpa [Variables.modeColumns] using modes (4 : Fin 7)
  have m5 : w 68 = 0 := by simpa [Variables.modeColumns] using modes (5 : Fin 7)
  have m6 : w 69 = 0 := by simpa [Variables.modeColumns] using modes (6 : Fin 7)
  have rotations := theta_rotations hp h active theta
  have r0 := rotations (0 : Fin 5); have r1 := rotations (1 : Fin 5)
  have r2 := rotations (2 : Fin 5); have r3 := rotations (3 : Fin 5)
  have r4 := rotations (4 : Fin 5)
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
  fin_cases operation <;> fin_cases limb <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      m0, m1, m2, theta, m4, m5, m6, r0, r1, r2, r3, r4, limbOffsets] at a b c ⊢
  all_goals exact ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩


end Airbender.Keccak.Proofs.ThetaRoutes
