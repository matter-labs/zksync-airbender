import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView2
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows2Part0
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns0 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry0 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      carryPad 0 (source0.map (Expression.eval (Verification.environment w))) := by
  change (entry0 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow0, frame_eq, source0_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values0, frame, source0Values, carryPad]

theorem columns1 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry1 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      plainPad (source1.map (Expression.eval (Verification.environment w))) := by
  change (entry1 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow1, frame_eq, source1_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values1, frame, source1Values, plainPad] <;> first
    | linear_combination (-w 327) * characteristic
    | linear_combination (256 * w 337 + 256 * w 361 - 2 * w 415) * characteristic
)

theorem columns2 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry2 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 2 w))) =
      carryPad 0 (source2.map (Expression.eval (Verification.environment w))) := by
  change (entry2 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 2 w).assignment)) = _
  rw [rawRow2, frame_eq, source2_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values2, frame, source2Values, carryPad]

theorem queries {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨0 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 2 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source0_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨0, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup0_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source0Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source0_eval w)
    · exact columns0 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source1_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨1, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup1_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source1Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source1_eval w)
    · exact columns1 compatible _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (2 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source2_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨2, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 2 w))
    rw [lookup2_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source2Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source2_eval w)
    · exact columns2 _ w

end Airbender.Blake2Round.Proofs.NativeDiagonalRows2Part0
