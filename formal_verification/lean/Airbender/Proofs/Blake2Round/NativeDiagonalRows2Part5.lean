import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView2
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows2Part5
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns15 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry15 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      plainPad (source12.map (Expression.eval (Verification.environment w))) := by
  change (entry15 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow15, frame_eq, source12_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values15, frame, source12Values, plainPad] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (512 * w 268 + 512 * w 289 + 2 * w 483) * characteristic
)

theorem columns16 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry16 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      carryPad 1 (source15.map (Expression.eval (Verification.environment w))) := by
  change (entry16 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow16, frame_eq, source15_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values16, frame, source15Values, carryPad]

theorem columns17 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry17 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      plainPad (source13.map (Expression.eval (Verification.environment w))) := by
  change (entry17 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow17, frame_eq, source13_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values17, frame, source13Values, plainPad] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (512 * w 271 + 512 * w 291 + 2 * w 481 + 61440 * w 265 + 61440 * w 287 + 61440 * w 483) * characteristic
)

theorem queries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨15 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 2 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source12_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨15, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup15_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · simpa [source12Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source12_eval w)
    · exact columns15 compatible _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source15_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨16, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup16_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 1 member
    · simpa [source15Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source15_eval w)
    · exact columns16 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source13_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨17, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup17_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · simpa [source13Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source13_eval w)
    · exact columns17 compatible _ w

end Airbender.Blake2Round.Proofs.NativeDiagonalRows2Part5
