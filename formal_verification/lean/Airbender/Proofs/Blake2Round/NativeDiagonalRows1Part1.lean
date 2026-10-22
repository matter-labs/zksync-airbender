import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView1
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows1Part1
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns3 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry3 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 1 w))) =
      plainPad (source3.map (Expression.eval (Verification.environment w))) := by
  change (entry3 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 1 w).assignment)) = _
  rw [rawRow3, frame_eq, source3_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values3, frame, source3Values, plainPad] <;> first
    | linear_combination (-w 286) * characteristic
    | linear_combination (256 * w 299 + 256 * w 323 - 2 * w 374) * characteristic
)

theorem columns4 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry4 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 1 w))) =
      combinedHighPad (source7.map (Expression.eval (Verification.environment w))) := by
  change (entry4 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 1 w).assignment)) = _
  rw [rawRow4, frame_eq, source7_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values4, frame, source7Values, combinedHighPad]

theorem columns5 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry5 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 1 w))) =
      plainPad (source4.map (Expression.eval (Verification.environment w))) := by
  change (entry5 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 1 w).assignment)) = _
  rw [rawRow5, frame_eq, source4_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values5, frame, source4Values, plainPad]

theorem queries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨3 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 1 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (3 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source3_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨3, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 1 w))
    rw [lookup3_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source3Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source3_eval w)
    · exact columns3 compatible _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source7_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨4, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 1 w))
    rw [lookup4_eq_mk]
    apply combined_high_membership hp (fun _ => Vector.replicate 7 0) member
    · simpa [source7Values] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source7_eval w)
    · exact columns4 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (1 : Fin 4) (4 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source4_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨5, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 1 w))
    rw [lookup5_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · simpa [source4Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source4_eval w)
    · exact columns5 _ w

end Airbender.Blake2Round.Proofs.NativeDiagonalRows1Part1
