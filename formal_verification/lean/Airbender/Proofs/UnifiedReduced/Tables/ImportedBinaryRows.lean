import Airbender.Proofs.Tables.RowViews
import Airbender.Proofs.UnifiedReduced.Tables.ImportedWideRows
import Airbender.Proofs.UnifiedReduced.Tables.ImportedSignRows
import Airbender.Proofs.UnifiedReduced.Tables.ImportedShiftColumns
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Proofs.Tables.ShiftPrefixRows

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem native_row_alias (kind : Fin 15) (data : TableData 10)
    (named : nativeFixedData kind = data) (n : Nat) :
    nativeFixedRow kind n = data.columns.map (fun column => (column.get? n).getD 0) := by
  cases named
  rfl

private theorem ordinary_row_alias (kind : Fin 7) (data : TableData 10)
    (named : shiftData kind = data) (n : Nat) :
    shiftRegionRow kind n = data.columns.map (fun column => (column.get? n).getD 0) := by
  cases named
  rfl

theorem imported_binary_case0 (n : Nat) (bound : n < 1) :
    nativeFixedRow 0 n = (shiftRegionRow 0 n).set 9 ((shiftRegionRow 0 n)[9]'(by decide)) (by decide) := by
  have zero : n = 0 := by omega
  subst n
  decide +kernel

theorem imported_binary_case1 (n : Nat) (bound : n < 256) :
    nativeFixedRow 1 n = (shiftRegionRow 1 n).set 9 ((shiftRegionRow 1 n)[9]'(by decide)) (by decide) := by
  have actual := imported_byte_sign_row ⟨n, bound⟩
  have ordinary := ShiftPrefix.sign_row n bound
  have full := Airbender.Setup.Proofs.unwrap_row _ _ _ actual
  have same := (native_row_alias 1 nativeByteSignData (by rfl) n).trans (full.trans ordinary.symm)
  simpa only [Vector.set_getElem_self] using same

theorem imported_binary_case2 (n : Nat) (bound : n < 65536) :
    nativeFixedRow 2 n = (shiftRegionRow 2 n).set 9 52 (by decide) := by
  have left : nativeFixedData 2 = nativeXorData := rfl
  have right : wideData 0 = nativeXorData := rfl
  have oldLeft : shiftData 2 = byteXorData := rfl
  have oldRight : ordinaryData 0 = byteXorData := rfl
  have native := native_row_alias 2 (wideData 0) (left.trans right.symm) n
  have ordinary := ordinary_row_alias 2 (ordinaryData 0) (oldLeft.trans oldRight.symm) n
  have values := imported_wide_row 0 n bound
  have tagged := congrArg (fun row : Vector Nat 10 => row.set 9 52 (by decide)) ordinary.symm
  exact native.trans (values.trans tagged)

theorem imported_binary_case3 (n : Nat) (bound : n < 65536) :
    nativeFixedRow 3 n = (shiftRegionRow 3 n).set 9 53 (by decide) := by
  have left : nativeFixedData 3 = nativeOrData := rfl
  have right : wideData 1 = nativeOrData := rfl
  have oldLeft : shiftData 3 = byteOrData := rfl
  have oldRight : ordinaryData 1 = byteOrData := rfl
  have native := native_row_alias 3 (wideData 1) (left.trans right.symm) n
  have ordinary := ordinary_row_alias 3 (ordinaryData 1) (oldLeft.trans oldRight.symm) n
  have values := imported_wide_row 1 n bound
  have tagged := congrArg (fun row : Vector Nat 10 => row.set 9 53 (by decide)) ordinary.symm
  exact native.trans (values.trans tagged)

theorem imported_binary_case4 (n : Nat) (bound : n < 65536) :
    nativeFixedRow 4 n = (shiftRegionRow 4 n).set 9 54 (by decide) := by
  have left : nativeFixedData 4 = nativeAndData := rfl
  have right : wideData 2 = nativeAndData := rfl
  have oldLeft : shiftData 4 = byteAndData := rfl
  have oldRight : ordinaryData 2 = byteAndData := rfl
  have native := native_row_alias 4 (wideData 2) (left.trans right.symm) n
  have ordinary := ordinary_row_alias 4 (ordinaryData 2) (oldLeft.trans oldRight.symm) n
  have values := imported_wide_row 2 n bound
  have tagged := congrArg (fun row : Vector Nat 10 => row.set 9 54 (by decide)) ordinary.symm
  exact native.trans (values.trans tagged)

theorem imported_binary_case5 (n : Nat) (bound : n < 65536) :
    nativeFixedRow 5 n = (shiftRegionRow 5 n).set 9 ((shiftRegionRow 5 n)[9]'(by decide)) (by decide) := by
  have ordinary := ordinary_row_alias 5 byteTruncateData (by rfl) n
  have same := (native_row_alias 5 nativeTruncationData (by rfl) n).trans
    ((imported_truncation_row n bound).trans ordinary.symm)
  simpa only [Vector.set_getElem_self] using same

theorem imported_binary_case6 (n : Nat) (_bound : n < 262144) :
    nativeFixedRow 6 n = (shiftRegionRow 6 n).set 9 ((shiftRegionRow 6 n)[9]'(by decide)) (by decide) := by
  have values := Airbender.Setup.Proofs.rows_agree nativeShiftData byteShiftData n
    (fun lane => imported_shift_column_get lane n)
  have same := (native_row_alias 6 nativeShiftData (by rfl) n).trans
    (values.trans (ordinary_row_alias 6 byteShiftData (by rfl) n).symm)
  simpa only [Vector.set_getElem_self] using same

/-- The native unified fixed regions project to the checked ordinary data,
    with only the three wide-binop tags changed. -/
theorem imported_binary_region (kind : Fin 7) (n : Nat)
    (bound : n < (nativeFixedData ⟨kind.val, Nat.lt_trans kind.isLt (by decide : 7 < 15)⟩).length) :
    nativeFixedRow ⟨kind.val, Nat.lt_trans kind.isLt (by decide : 7 < 15)⟩ n =
      (shiftRegionRow kind n).set 9
        (if kind.val = 2 then 52 else if kind.val = 3 then 53 else
          if kind.val = 4 then 54 else (shiftRegionRow kind n)[9]'(by decide)) (by decide) := by
  revert n
  fin_cases kind
  all_goals intro n bound
  · exact imported_binary_case0 n bound
  · exact imported_binary_case1 n bound
  · exact imported_binary_case2 n bound
  · exact imported_binary_case3 n bound
  · exact imported_binary_case4 n bound
  · exact imported_binary_case5 n bound
  · exact imported_binary_case6 n bound

end Airbender.UnifiedReduced.Setup.Proofs
