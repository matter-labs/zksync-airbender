import Airbender.Proofs.UnifiedReduced.Tables.ImportedShiftColumn7
import Airbender.Proofs.UnifiedReduced.Tables.ImportedShiftColumn6
import Airbender.Proofs.UnifiedReduced.Tables.ImportedShiftColumn5
import Airbender.Proofs.UnifiedReduced.Tables.ImportedShiftColumn3
import Airbender.Data.Setup.UnifiedReduced.Native.ShiftData
import Airbender.Data.Tables.Shift.ShiftData
import Airbender.Proofs.Tables.ColumnAgreement
import Mathlib.Tactic.FinCases

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem column_get_transport (actualA actualB namedA namedB : Column)
    (left : actualA = namedA) (right : actualB = namedB)
    (values : namedA.get? n = namedB.get? n) : actualA.get? n = actualB.get? n := by
  cases left
  cases right
  exact values

/-- Independently imported native columns agree at every index, including
    the differently compressed operation/output tails. -/
theorem imported_shift_column_get (lane : Fin 10) (n : Nat) :
    nativeShiftData.columns[lane].get? n = byteShiftData.columns[lane].get? n := by
  fin_cases lane
  · apply column_get_transport _ _ nativeShiftColumn0 byteShiftColumn0 (by rfl) (by rfl)
    exact congrArg (fun column : Column => column.get? n)
      (show nativeShiftColumn0 = byteShiftColumn0 from rfl)
  · apply column_get_transport _ _ nativeShiftColumn1 byteShiftColumn1 (by rfl) (by rfl)
    exact congrArg (fun column : Column => column.get? n)
      (show nativeShiftColumn1 = byteShiftColumn1 from rfl)
  · apply column_get_transport _ _ nativeShiftColumn2 byteShiftColumn2 (by rfl) (by rfl)
    exact congrArg (fun column : Column => column.get? n)
      (show nativeShiftColumn2 = byteShiftColumn2 from rfl)
  · apply column_get_transport _ _ nativeShiftColumn3 byteShiftColumn3 (by rfl) (by rfl)
    exact blocksAgree_sound _ _ shift_column3_agreement n
  · apply column_get_transport _ _ nativeShiftColumn4 byteShiftColumn4 (by rfl) (by rfl)
    exact congrArg (fun column : Column => column.get? n)
      (show nativeShiftColumn4 = byteShiftColumn4 from rfl)
  · apply column_get_transport _ _ nativeShiftColumn5 byteShiftColumn5 (by rfl) (by rfl)
    exact shift_column5_get n
  · apply column_get_transport _ _ nativeShiftColumn6 byteShiftColumn6 (by rfl) (by rfl)
    exact shift_column6_get n
  · apply column_get_transport _ _ nativeShiftColumn7 byteShiftColumn7 (by rfl) (by rfl)
    exact shift_column7_get n
  · apply column_get_transport _ _ nativeShiftColumn8 byteShiftColumn8 (by rfl) (by rfl)
    exact congrArg (fun column : Column => column.get? n)
      (show nativeShiftColumn8 = byteShiftColumn8 from rfl)
  · apply column_get_transport _ _ nativeShiftColumn9 byteShiftColumn9 (by rfl) (by rfl)
    exact congrArg (fun column : Column => column.get? n)
      (show nativeShiftColumn9 = byteShiftColumn9 from rfl)

end Airbender.UnifiedReduced.Setup.Proofs
