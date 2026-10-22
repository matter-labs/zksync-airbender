import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeDiagonalRows3Part4

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Project one native diagonal call into the unchanged G arithmetic queries. -/
theorem native_diagonal_queries_3_part_4 {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨12 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 3 w)) := by
  exact NativeDiagonalRows3Part4.queries hp compatible h i

end Airbender.Blake2Round.Proofs
