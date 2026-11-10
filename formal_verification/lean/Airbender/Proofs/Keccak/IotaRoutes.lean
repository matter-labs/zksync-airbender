import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Keccak.Iota
import Airbender.Proofs.Keccak.Tags
import Airbender.Proofs.Constraints.Core
import Mathlib.Tactic.LinearCombination

namespace Airbender.Keccak.Proofs.IotaRoutes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def nativeLimbs (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 4, start + 5]
private def temporary (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 2, start + 3]
private def aColumns : Vector (Vector Nat 4) 5 :=
  #v[nativeLimbs 15, nativeLimbs 17, temporary 90, temporary 94, temporary 98]
private def bColumns : Vector (Vector Nat 4) 5 :=
  #v[temporary 86, nativeLimbs 23, nativeLimbs 31, nativeLimbs 39, nativeLimbs 47]
private def cColumns : Vector (Vector Nat 4) 5 :=
  #v[nativeLimbs 17, temporary 90, temporary 94, temporary 98, nativeLimbs 57]
private def packed {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 4) : Nat :=
  (w columns[0]).val + 65536 * ((w columns[1]).val +
    65536 * ((w columns[2]).val + 65536 * (w columns[3]).val))

theorem checked {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 7)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (selected : w 63 = 1) (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + 2 * limb.val) +
      256 * w (103 + 24 * operation.val + 2 * limb.val) = w aColumns[operation][limb] ∧
    w (110 + 24 * operation.val + 2 * limb.val) +
      256 * w (111 + 24 * operation.val + 2 * limb.val) = w bColumns[operation][limb] ∧
    w (118 + 24 * operation.val + 2 * limb.val) +
      256 * w (119 + 24 * operation.val + 2 * limb.val) = w cColumns[operation][limb] := by
  have modes := selected_modes hp h active (0 : Fin 7) selected
  have m1 := modes (1 : Fin 7); have m2 := modes (2 : Fin 7); have m3 := modes (3 : Fin 7)
  have m4 := modes (4 : Fin 7); have m5 := modes (5 : Fin 7); have m6 := modes (6 : Fin 7)
  simp [Variables.modeColumns] at m1 m2 m3 m4 m5 m6
  have rotations (i : Fin 5) : w (80 + i.val) = 0 := by
    have equation := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
    fin_cases i <;> simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, m4] using equation.symm
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
  fin_cases operation <;> fin_cases limb <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected, m1, m2, m3, m4, m5, m6,
      r0, r1, r2, r3, r4, aColumns, bColumns, cColumns, nativeLimbs, temporary] at a b c ⊢
  all_goals exact ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩

end Airbender.Keccak.Proofs.IotaRoutes
