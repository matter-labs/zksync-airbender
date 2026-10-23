import Airbender.Proofs.Blake2Round.NativeColumnValues3Part4
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView3
import Airbender.Proofs.Blake2Round.NativeCombinedTransfer

namespace Airbender.Blake2Round.Proofs.NativeColumnRows3Part4
open Blake2G.Proofs.FrameQueryShapes NativeColumnView3
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
      ⟨12 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeColumnAssignment 3 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (11 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source11_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨12, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 3 w))
    rw [lookup12_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source11Values, carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source11_eval w)
    · exact columns12 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (9 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source9_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨13, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 3 w))
    rw [lookup13_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [source9Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source9_eval w)
    · exact columns13 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .column (3 : Fin 4) (14 : Fin 16),
        by rw [lookup_count]; decide⟩
    rw [source14_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨14, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeColumnAssignment 3 w))
    rw [lookup14_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 1 member
    · simpa [source14Values, plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source14_eval w)
    · exact columns14 _ w

end Airbender.Blake2Round.Proofs.NativeColumnRows3Part4
