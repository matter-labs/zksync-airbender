import Airbender.Proofs.Blake2Round.NativeColumnValues1Part3
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView1
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer

namespace Airbender.Blake2Round.Proofs.NativeColumnRows1Part3
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
      ⟨9 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeColumnAssignment 1 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (1 : Fin 4) (7 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source7_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨9, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 1 w))
    rw [lookup9_eq_mk]
    apply combined_low_membership hp (fun _ => Vector.replicate 7 0) member
    · simpa [source7Values] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source7_eval w)
    · exact columns9 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (1 : Fin 4) (10 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source10_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨10, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 1 w))
    rw [lookup10_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source10Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source10_eval w)
    · exact columns10 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (1 : Fin 4) (8 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source8_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨11, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 1 w))
    rw [lookup11_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source8Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source8_eval w)
    · exact columns11 _ w

end Airbender.Blake2Round.Proofs.NativeColumnRows1Part3
