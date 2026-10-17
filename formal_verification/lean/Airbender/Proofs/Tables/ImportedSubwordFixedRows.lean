import Airbender.Proofs.Tables.ImportedSubwordKeys
import Airbender.Proofs.Tables.ImportedStoreClear
import Airbender.Proofs.Tables.ImportedLoadHalf
import Airbender.Proofs.Tables.ImportedLoadByteLow
import Airbender.Proofs.Tables.ImportedLoadByteHigh
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.SubwordFixed
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def fixedOutputs (kind : Fin 4) (n : Nat) : Nat × Nat :=
  if kind.val = 0 then (subwordStoreContribution false n, 0)
  else if kind.val = 1 then (subwordStoreContribution true n, 0)
  else if kind.val = 2 then subwordLoadLimbs false n else subwordLoadLimbs true n

theorem loadByte_outputs (n : Nat) (bound : n < 262144) :
    loadByteData.columns[1].get? n = some (subwordLoadLimbs true n).1 ∧
      loadByteData.columns[2].get? n = some (subwordLoadLimbs true n).2 := by
  rw [byte_meaning n bound]
  exact ⟨loadByte_low n bound, loadByte_high n bound⟩

private theorem outputs (kind : Fin 4) (n : Nat)
    (bound : n < (subwordFixedData kind).length) :
    (subwordFixedData kind).columns[1].get? n = some (fixedOutputs kind n).1 ∧
      (subwordFixedData kind).columns[2].get? n = some (fixedOutputs kind n).2 := by
  fin_cases kind
  · exact ⟨storePlace_output n bound, store_high 0 n bound⟩
  · exact ⟨storeClear_output n bound, store_high 1 n bound⟩
  · exact loadHalf_outputs n bound
  · exact loadByte_outputs n bound

/-- All physical fields of the four imported fixed regions, with their native IDs. -/
theorem fixed_row (kind : Fin 4) (n : Nat) (bound : n < (subwordFixedData kind).length) :
    subwordFixedRow kind n = subwordDataRow n (fixedOutputs kind n).1
      (fixedOutputs kind n).2 (subwordFixedRegion kind).id := by
  have values := outputs kind n bound
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [subwordFixedRow, subwordDataRow, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · exact congrArg (fun v => v.getD 0) (fixed_key kind n bound)
  · exact congrArg (fun v => v.getD 0) values.1
  · exact congrArg (fun v => v.getD 0) values.2
  · exact congrArg (fun v => v.getD 0) (fixed_padding kind 0 n bound)
  · exact congrArg (fun v => v.getD 0) (fixed_padding kind 1 n bound)
  · exact congrArg (fun v => v.getD 0) (fixed_padding kind 2 n bound)
  · exact congrArg (fun v => v.getD 0) (fixed_padding kind 3 n bound)
  · exact congrArg (fun v => v.getD 0) (fixed_padding kind 4 n bound)
  · exact congrArg (fun v => v.getD 0) (fixed_tag kind n bound)

/-- The native disabled row retains every physical zero field. -/
theorem zero_row : subwordZeroData.columns.map (fun column => (column.get? 0).getD 0) =
    (#v[0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector Nat 9) := by decide +kernel

/-- The natural real-row view agrees with the imported native field row. -/
theorem native_cast (kind : Fin 4) (index : Fin (subwordFixedData kind).length) :
    (subwordFixedRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((subwordFixedData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus)) := by
  have offset : (subwordFixedData kind).offset = 0 := by fin_cases kind <;> rfl
  apply Vector.ext
  intro lane hLane
  simp [subwordFixedRow, TableData.row, offset, signedValue_cast]

end Airbender.Verification.SubwordFixed
