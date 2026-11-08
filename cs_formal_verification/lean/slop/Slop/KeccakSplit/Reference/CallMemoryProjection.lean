import Slop.KeccakSplit.Reference.CallDestinations
import Slop.KeccakSplit.Reference.CallValues

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 65536

private theorem control_word_bound (index : Fin 361) : controlAt index.val < 2 ^ 32 := by
  have indexBound := index.isLt
  by_cases last : index.val = 360
  · norm_num [controlAt, last, encode, Kind.mode]
  · unfold controlAt
    rw [ite_eq_right last]
    cases kindAt index.val <;> simp only [encode, Kind.mode]
    all_goals have remainder := Nat.mod_lt index.val (by decide : 0 < 5)
    all_goals norm_num only [Nat.reducePow]
    all_goals omega

/-- Every live reference lane half occurs in the complete declared write list. -/
theorem written_lane_member (index : Fin 361) (pointer : BitVec 32) (output : Vector Nat 7)
    (lane : Fin 7) (live : lane.val < slotCount (kindAt index.val)) (high : Bool) :
    (laneCell pointer (slots index)[lane] high, half output[lane] high) ∈ writes index pointer output := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨lane.val, List.mem_range.mpr live, ?_⟩
  simp only [lane.isLt, ↓reduceDIte]
  cases high <;> simp only [Fin.getElem_fin, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]

end Airbender.Keccak.Split.Call.Proofs
