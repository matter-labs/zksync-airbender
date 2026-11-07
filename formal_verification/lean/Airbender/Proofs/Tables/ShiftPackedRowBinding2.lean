import Airbender.Proofs.Tables.ShiftPackedRowData

namespace Airbender.Verification.ShiftPackedReference
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def rowsCheck2 : Bool :=
  (List.range 1024).all fun row => numericRow 2 row == expectedRow 2 row

theorem rows_checked2 : rowsCheck2 = true := by decide +kernel

end Airbender.Verification.ShiftPackedReference
