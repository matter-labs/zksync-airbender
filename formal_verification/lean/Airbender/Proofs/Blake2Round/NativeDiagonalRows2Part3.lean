import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView2
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows2Part3
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns9 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry9 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      combinedLowPad (source7.map (Expression.eval (Verification.environment w))) := by
  change (entry9 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow9, frame_eq, source7_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values9, frame, source7Values, combinedLowPad, Arithmetic.combinedLow_as_value] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (16 * w 271 + 16 * w 291) * characteristic
)

theorem columns10 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry10 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      carryPad 0 (source10.map (Expression.eval (Verification.environment w))) := by
  change (entry10 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow10, frame_eq, source10_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values10, frame, source10Values, carryPad]

theorem columns11 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry11 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      plainPad (source8.map (Expression.eval (Verification.environment w))) := by
  change (entry11 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow11, frame_eq, source8_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values11, frame, source8Values, plainPad] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (256 * w 337 + 256 * w 361) * characteristic
)

theorem queries {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨9 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 2 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source7_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨9, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup9_eq_mk]
    apply combined_low_membership hp (fun _ => Vector.replicate 7 0) member
    · simpa [source7Values] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source7_eval w)
    · exact columns9 compatible _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source10_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨10, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup10_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source10Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source10_eval w)
    · exact columns10 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source8_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨11, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup11_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source8Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source8_eval w)
    · exact columns11 compatible _ w

end Airbender.Blake2Round.Proofs.NativeDiagonalRows2Part3
