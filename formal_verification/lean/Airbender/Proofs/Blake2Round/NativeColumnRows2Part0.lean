import Airbender.Proofs.Blake2Round.NativeColumnValues2Part0
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView2
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer

namespace Airbender.Blake2Round.Proofs.NativeColumnRows2Part0
open Blake2G.Proofs.FrameQueryShapes NativeColumnView2
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
      ⟨0 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeColumnAssignment 2 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (0 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source0_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨0, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 2 w))
    rw [lookup0_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source0Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source0_eval w)
    · exact columns0 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (1 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source1_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨1, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 2 w))
    rw [lookup1_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source1Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source1_eval w)
    · exact columns1 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (2 : Fin 4) (2 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source2_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨2, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 2 w))
    rw [lookup2_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source2Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source2_eval w)
    · exact columns2 _ w

end Airbender.Blake2Round.Proofs.NativeColumnRows2Part0
