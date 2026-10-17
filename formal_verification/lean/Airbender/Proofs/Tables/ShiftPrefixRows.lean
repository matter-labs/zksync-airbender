import Airbender.Proofs.Tables.SignColumns
import Airbender.Review.Helpers.Tables.ShiftData
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.ShiftPrefix
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem zero_row : shiftRegionRow 0 0 =
    (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector Nat 10) := by decide +kernel

theorem sign_row (n : Nat) (bound : n < 256) :
    shiftRegionRow 1 n = #v[n, if n < 128 then 0 else 255, 0, 0, 0, 0, 0, 0, 0, 3] := by
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [shiftRegionRow, shiftData, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Vector.getElem_map]
  · exact congrArg (fun v => v.getD 0) (SignColumns.key n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.extension n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.padding 0 n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.padding 1 n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.padding 2 n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.padding 3 n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.padding 4 n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.padding 5 n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.padding 6 n bound)
  · exact congrArg (fun v => v.getD 0) (SignColumns.tag n bound)

end Airbender.Verification.ShiftPrefix
