import Airbender.Proofs.GKRProtocol.HelperCertificate

namespace Airbender.Compiler.HelperProjectionChecks
set_option warningAsError true

theorem map_getD_prefix (entries : List α) (fallback : α) (size : Nat)
    (bound : size ≤ entries.length) :
    (List.range size).map (fun index => (entries[index]?).getD fallback) = entries.take size := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, Nat.min_eq_left bound]
  · intro index leftBound rightBound
    simp only [List.length_map, List.length_range] at leftBound
    have inside : index < entries.length := Nat.lt_of_lt_of_le leftBound bound
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    simp [inside]

end Airbender.Compiler.HelperProjectionChecks
