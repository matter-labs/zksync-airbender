import Airbender.Proofs.Blake2Round.NativeColumnRows1Part0
import Airbender.Proofs.Blake2Round.NativeColumnRows1Part1
import Airbender.Proofs.Blake2Round.NativeColumnRows1Part2
import Airbender.Proofs.Blake2Round.NativeColumnRows1Part3
import Airbender.Proofs.Blake2Round.NativeColumnRows1Part4
import Airbender.Proofs.Blake2Round.NativeColumnRows1Part5

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Project one native column call into the unchanged G arithmetic queries. -/
theorem native_column_queries_1 {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 18) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; exact i.isLt⟩).Contains
        (Verification.environment (nativeColumnAssignment 1 w)) := by
  by_cases early0 : i.val < 3
  · have query := NativeColumnRows1Part0.queries hp h ⟨i.val - 0, by have := i.isLt; omega⟩
    have index : 0 + (i.val - 0) = i.val := by omega
    simpa only [index] using query
  by_cases early1 : i.val < 6
  · have query := NativeColumnRows1Part1.queries hp h ⟨i.val - 3, by have := i.isLt; omega⟩
    have index : 3 + (i.val - 3) = i.val := by omega
    simpa only [index] using query
  by_cases early2 : i.val < 9
  · have query := NativeColumnRows1Part2.queries hp h ⟨i.val - 6, by have := i.isLt; omega⟩
    have index : 6 + (i.val - 6) = i.val := by omega
    simpa only [index] using query
  by_cases early3 : i.val < 12
  · have query := NativeColumnRows1Part3.queries hp h ⟨i.val - 9, by have := i.isLt; omega⟩
    have index : 9 + (i.val - 9) = i.val := by omega
    simpa only [index] using query
  by_cases early4 : i.val < 15
  · have query := NativeColumnRows1Part4.queries hp h ⟨i.val - 12, by have := i.isLt; omega⟩
    have index : 12 + (i.val - 12) = i.val := by omega
    simpa only [index] using query
  have query := NativeColumnRows1Part5.queries hp h ⟨i.val - 15, by have := i.isLt; omega⟩
  have index : 15 + (i.val - 15) = i.val := by omega
  simpa only [index] using query

end Airbender.Blake2Round.Proofs
