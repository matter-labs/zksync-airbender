import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView0
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows0Part2
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView0
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns6 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry6 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      combinedLowPad (source6.map (Expression.eval (Verification.environment w))) := by
  change (entry6 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [rawRow6, frame_eq, source6_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values6, frame, source6Values, combinedLowPad, Arithmetic.combinedLow_as_value] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (16 * w 348 + 16 * w 369) * characteristic
)

theorem columns7 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry7 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      combinedHighPad (source6.map (Expression.eval (Verification.environment w))) := by
  change (entry7 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [rawRow7, frame_eq, source6_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values7, frame, source6Values, combinedHighPad]

theorem columns8 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry8 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      plainPad (source5.map (Expression.eval (Verification.environment w))) := by
  change (entry8 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [rawRow8, frame_eq, source5_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values8, frame, source5Values, plainPad]

theorem queries {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨6 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 0 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source6_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨6, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 0 w))
    rw [lookup6_eq_mk]
    apply combined_low_membership hp (fun _ => Vector.replicate 7 0) member
    · simpa [source6Values] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source6_eval w)
    · exact columns6 compatible _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source6_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨7, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 0 w))
    rw [lookup7_eq_mk]
    apply combined_high_membership hp (fun _ => Vector.replicate 7 0) member
    · simpa [source6Values] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source6_eval w)
    · exact columns7 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source5_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨8, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 0 w))
    rw [lookup8_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · simpa [source5Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source5_eval w)
    · exact columns8 _ w

end Airbender.Blake2Round.Proofs.NativeDiagonalRows0Part2
