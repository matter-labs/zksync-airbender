import Airbender.Proofs.Blake2Round.NativeColumnValues0Part2
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView0
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer

namespace Airbender.Blake2Round.Proofs.NativeColumnRows0Part2
open Blake2G.Proofs.FrameQueryShapes NativeColumnView0
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem queries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨6 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeColumnAssignment 0 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (0 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source6_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨6, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 0 w))
    rw [lookup6_eq_mk]
    apply combined_low_membership hp (fun _ => Vector.replicate 7 0) member
    · simpa [source6Values] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source6_eval w)
    · exact columns6 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (0 : Fin 4) (6 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source6_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨7, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 0 w))
    rw [lookup7_eq_mk]
    apply combined_high_membership hp (fun _ => Vector.replicate 7 0) member
    · simpa [source6Values] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source6_eval w)
    · exact columns7 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (0 : Fin 4) (5 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source5_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨8, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 0 w))
    rw [lookup8_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · simpa [source5Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source5_eval w)
    · exact columns8 _ w

end Airbender.Blake2Round.Proofs.NativeColumnRows0Part2
