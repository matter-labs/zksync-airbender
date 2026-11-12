module
public import Proven.KeccakSplit.Reference.CallDestinations
public import Proven.KeccakSplit.Reference.CallValues

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 65536

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
