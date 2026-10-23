import Airbender.Proofs.Blake2Round.NativeColumnValues1Part5
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView1
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer

namespace Airbender.Blake2Round.Proofs.NativeColumnRows1Part5
open Blake2G.Proofs.FrameQueryShapes NativeColumnView1
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
      ⟨15 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeColumnAssignment 1 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (1 : Fin 4) (12 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source12_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨15, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 1 w))
    rw [lookup15_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · simpa [source12Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source12_eval w)
    · exact columns15 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (1 : Fin 4) (15 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source15_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨16, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 1 w))
    rw [lookup16_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 1 member
    · simpa [source15Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source15_eval w)
    · exact columns16 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (1 : Fin 4) (13 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source13_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨17, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 1 w))
    rw [lookup17_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 2 member
    · simpa [source13Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source13_eval w)
    · exact columns17 _ w

end Airbender.Blake2Round.Proofs.NativeColumnRows1Part5
