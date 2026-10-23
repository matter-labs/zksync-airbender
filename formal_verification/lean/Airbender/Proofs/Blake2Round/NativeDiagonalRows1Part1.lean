import Airbender.Proofs.Blake2Round.NativeDiagonalValues1Part1
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
