import Airbender.Review.Helpers.Tables.SmallRange
import Airbender.Proofs.Mersenne31
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification

/-- Exact native pair membership retains both byte bounds and its third zero. -/
theorem small_range_values {p : Nat} [Fact p.Prime] {first second padding : ZMod p}
    (holds : smallRangeTable.Contains #[] #v[first, second, padding]) :
    first.val < 256 ∧ second.val < 256 ∧ padding = 0 := by
  change ∃ i : Fin 65536, #v[first, second, padding] = (smallRangeRow i).map Nat.cast at holds
  obtain ⟨i, same⟩ := holds
  have a : first = (i.val / 256 : Nat) := by
    simpa [smallRangeRow] using congrArg (fun v : Vector (ZMod p) 3 => v[0]) same
  have b : second = (i.val % 256 : Nat) := by
    simpa [smallRangeRow] using congrArg (fun v : Vector (ZMod p) 3 => v[1]) same
  have bound := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · rw [a, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  · rw [b, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))
  · simpa [smallRangeRow] using congrArg (fun v : Vector (ZMod p) 3 => v[2]) same

theorem small_range_contains {p : Nat} [Fact p.Prime] {first second padding : ZMod p}
    (left : first.val < 256) (right : second.val < 256) (zero : padding = 0) :
    smallRangeTable.Contains #[] #v[first, second, padding] := by
  change ∃ i : Fin 65536, #v[first, second, padding] = (smallRangeRow i).map Nat.cast
  have bound : first.val * 256 + second.val < 65536 := by omega
  refine ⟨⟨first.val * 256 + second.val, bound⟩, ?_⟩
  have quotient : (first.val * 256 + second.val) / 256 = first.val := by omega
  have remainder : (first.val * 256 + second.val) % 256 = second.val := by omega
  ext lane small
  interval_cases lane <;> simp [smallRangeRow, quotient, remainder, zero]

end Airbender.Verification
