import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeDiagonalQueries2Part0
import Airbender.Proofs.Blake2Round.NativeDiagonalQueries2Part1
import Airbender.Proofs.Blake2Round.NativeDiagonalQueries2Part2
import Airbender.Proofs.Blake2Round.NativeDiagonalQueries2Part3
import Airbender.Proofs.Blake2Round.NativeDiagonalQueries2Part4
import Airbender.Proofs.Blake2Round.NativeDiagonalQueries2Part5

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
/-- Project one native diagonal call into the unchanged G arithmetic queries. -/
theorem native_diagonal_queries_2 {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 18) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; exact i.isLt⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 2 w)) := by
  fin_cases i
  · exact native_diagonal_queries_2_part_0 hp compatible h 0
  · exact native_diagonal_queries_2_part_0 hp compatible h 1
  · exact native_diagonal_queries_2_part_0 hp compatible h 2
  · exact native_diagonal_queries_2_part_1 hp compatible h 0
  · exact native_diagonal_queries_2_part_1 hp compatible h 1
  · exact native_diagonal_queries_2_part_1 hp compatible h 2
  · exact native_diagonal_queries_2_part_2 hp compatible h 0
  · exact native_diagonal_queries_2_part_2 hp compatible h 1
  · exact native_diagonal_queries_2_part_2 hp compatible h 2
  · exact native_diagonal_queries_2_part_3 hp compatible h 0
  · exact native_diagonal_queries_2_part_3 hp compatible h 1
  · exact native_diagonal_queries_2_part_3 hp compatible h 2
  · exact native_diagonal_queries_2_part_4 hp compatible h 0
  · exact native_diagonal_queries_2_part_4 hp compatible h 1
  · exact native_diagonal_queries_2_part_4 hp compatible h 2
  · exact native_diagonal_queries_2_part_5 hp compatible h 0
  · exact native_diagonal_queries_2_part_5 hp compatible h 1
  · exact native_diagonal_queries_2_part_5 hp compatible h 2

end Airbender.Blake2Round.Proofs
