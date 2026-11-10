import Airbender.Proofs.Tables.ShiftPackedRowData

namespace Airbender.Verification.ShiftPackedReference
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def rowsCheck1 : Bool :=
  (List.range 1024).all fun row => numericRow 1 row == expectedRow 1 row

theorem rows_checked1 : rowsCheck1 = true := by decide +kernel

end Airbender.Verification.ShiftPackedReference
