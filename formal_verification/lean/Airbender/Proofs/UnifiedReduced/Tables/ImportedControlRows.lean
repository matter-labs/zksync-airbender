import Airbender.Proofs.UnifiedReduced.Tables.ImportedSharedData
import Airbender.Proofs.Tables.ImportedPairRows
import Mathlib.Tactic.IntervalCases

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- The complete native register-zero region reuses the independently checked
    ordinary data, including every padding field and discriminator. -/
theorem imported_register_zero_row (n : Nat) (bound : n < 131072) :
    nativeRegisterZeroData.columns.map (fun column => (column.get? n).getD 0) =
      (#v[n, if n = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1] : Vector Nat 10) := by
  rw [imported_register_zero_data]
  have values := ImportedPairRows.jump_pair_columns 0 ⟨n, bound⟩
  have pair := ImportedPairs.regZero_row ⟨n, bound⟩
  have key : (regZeroData.columns[0].get? n).getD 0 = n := by
    simpa only [setupPairRow, show regZeroData.offset = 0 from rfl, Nat.zero_add] using
      congrArg Prod.fst pair
  have output : (regZeroData.columns[1].get? n).getD 0 = (if n = 0 then 1 else 0) := by
    simpa only [setupPairRow, show regZeroData.offset = 0 from rfl, Nat.zero_add] using
      congrArg Prod.snd pair
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · exact key
  · exact output
  · exact congrArg (fun value => value.getD 0) (values.2.1 0)
  · exact congrArg (fun value => value.getD 0) (values.2.1 1)
  · exact congrArg (fun value => value.getD 0) (values.2.1 2)
  · exact congrArg (fun value => value.getD 0) (values.2.1 3)
  · exact congrArg (fun value => value.getD 0) (values.2.1 4)
  · exact congrArg (fun value => value.getD 0) (values.2.1 5)
  · exact congrArg (fun value => value.getD 0) (values.2.1 6)
  · exact congrArg (fun value => value.getD 0) values.2.2

/-- Every field of native cleanup ID2 is the independently checked actual row. -/
theorem imported_cleanup_row (n : Nat) (bound : n < 65536) :
    nativeCleanupData.columns.map (fun column => (column.get? n).getD 0) =
      (#v[n, n / 2 % 2, n - n % 4, 0, 0, 0, 0, 0, 0, 2] : Vector Nat 10) := by
  rw [imported_cleanup_data]
  have values := ImportedPairRows.cleanup_columns ⟨n, bound⟩
  have key : (jumpCleanupData.columns[0].get? n).getD 0 = n := by
    simpa only [setupTripleRow, show jumpCleanupData.offset = 0 from rfl, Nat.zero_add] using
      congrArg Prod.fst values.1
  have bit : (jumpCleanupData.columns[1].get? n).getD 0 = n / 2 % 2 := by
    simpa only [setupTripleRow, show jumpCleanupData.offset = 0 from rfl, Nat.zero_add] using
      congrArg (fun row => row.2.1) values.1
  have cleaned : (jumpCleanupData.columns[2].get? n).getD 0 = n - n % 4 := by
    simpa only [setupTripleRow, show jumpCleanupData.offset = 0 from rfl, Nat.zero_add] using
      congrArg (fun row => row.2.2) values.1
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · exact key
  · exact bit
  · exact cleaned
  · exact congrArg (fun value => value.getD 0) (values.2.1 0)
  · exact congrArg (fun value => value.getD 0) (values.2.1 1)
  · exact congrArg (fun value => value.getD 0) (values.2.1 2)
  · exact congrArg (fun value => value.getD 0) (values.2.1 3)
  · exact congrArg (fun value => value.getD 0) (values.2.1 4)
  · exact congrArg (fun value => value.getD 0) (values.2.1 5)
  · exact congrArg (fun value => value.getD 0) values.2.2

end Airbender.UnifiedReduced.Setup.Proofs
