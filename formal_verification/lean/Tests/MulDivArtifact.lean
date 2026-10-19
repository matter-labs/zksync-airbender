import Airbender.Proofs.MulDiv.ByteBounds

namespace Tests.MulDivArtifact
open Airbender Verification

/-- Both byte endpoints are actual members, including the last exported row. -/
theorem endpoints : smallRangeTable.Contains #[] #v[(0 : ZMod mersenne31Modulus),255,0] ∧
    smallRangeTable.Contains #[] #v[(255 : ZMod mersenne31Modulus),255,0] := by
  constructor <;> apply small_range_contains <;> decide

theorem first_overflow : ¬ smallRangeTable.Contains #[] #v[(256 : ZMod mersenne31Modulus),0,0] := by
  intro h
  have bound := (small_range_values h).1
  exact (by decide : ¬ (256 : ZMod mersenne31Modulus).val < 256) bound

theorem second_overflow : ¬ smallRangeTable.Contains #[] #v[(0 : ZMod mersenne31Modulus),256,0] := by
  intro h
  have bound := (small_range_values h).2.1
  exact (by decide : ¬ (256 : ZMod mersenne31Modulus).val < 256) bound

theorem third_column : ¬ smallRangeTable.Contains #[] #v[(0 : ZMod mersenne31Modulus),0,1] := by
  intro h
  have zero := (small_range_values h).2.2
  norm_num at zero

theorem wrong_tag : ¬ ∃ i : Fin 65536,
    (#v[(0 : ZMod mersenne31Modulus),0,0]).push 9 = NativeSmallRange.data.row i := by
  rintro ⟨i,same⟩
  have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
  apply (by decide : (9 : ZMod mersenne31Modulus) ≠ 8)
  simpa [Setup.TableData.row,MulDiv.Proofs.native_small_range_rows,Vector.map_push] using tag

end Tests.MulDivArtifact
