import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Keccak.Rho
import Airbender.Proofs.Keccak.Tags
import Airbender.Proofs.Constraints.Core
import Airbender.Proofs.Arithmetic.LaneRotation
import Mathlib.Tactic.LinearCombination

namespace Airbender.Keccak.Proofs.Rho
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4800000

abbrev rotations := rhoRotations

def limbOffset : Vector Nat 4 := #v[0, 1, 4, 5]

theorem rho_routes {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 7)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (column : Fin 5)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (selected : w 67 = 1)
    (iterations : ∀ i : Fin 5, w Variables.iterationColumns[i] = if i = column then 1 else 0)
    (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + limb.val) =
      w (15 + 8 * operation.val + limbOffset[limb]) +
        65536 * ((rotations[column][operation].val % 16 : Nat) : ZMod p) ∧
    w (118 + 24 * operation.val + (rotationSource rotations[column][operation] limb).val) +
      w (110 + 24 * operation.val +
        (rotationPrevious (rotationSource rotations[column][operation] limb)).val) =
      w (17 + 8 * operation.val + limbOffset[limb]) := by
  have modes := selected_modes hp h active (4 : Fin 7) selected
  have m0 := modes (0 : Fin 7); have m1 := modes (1 : Fin 7)
  have m2 := modes (2 : Fin 7); have m3 := modes (3 : Fin 7)
  have m5 := modes (5 : Fin 7); have m6 := modes (6 : Fin 7)
  have flags (i : Fin 5) : w (80 + i.val) = if i = column then 1 else 0 := by
    have equation := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
    have equal : w (80 + i.val) = w Variables.iterationColumns[i] := by
      fin_cases i <;> simp [Variables.iterationColumns] at ⊢
      all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected] at equation
      all_goals linear_combination -equation
    exact equal.trans (iterations i)
  have r0 := flags (0 : Fin 5); have r1 := flags (1 : Fin 5)
  have r2 := flags (2 : Fin 5); have r3 := flags (3 : Fin 5); have r4 := flags (4 : Fin 5)
  change w 80 = _ at r0
  change w 81 = _ at r1
  change w 82 = _ at r2
  change w 83 = _ at r3
  change w 84 = _ at r4
  have a := Verification.assertion_of_holds h
    ⟨20 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  have c := Verification.assertion_of_holds h
    ⟨22 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  simp [Variables.modeColumns] at m0 m1 m2 m3 m5 m6
  fin_cases operation <;> fin_cases limb
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, m0, m1, m2, m3, selected, m5, m6,
    r0, r1, r2, r3, r4] at a c
  all_goals fin_cases column
  all_goals simp [rotations, rhoRotations, limbOffset, rotationSource, rotationPrevious] at a c ⊢
  all_goals exact ⟨by linear_combination a, by linear_combination c⟩


end Airbender.Keccak.Proofs.Rho
