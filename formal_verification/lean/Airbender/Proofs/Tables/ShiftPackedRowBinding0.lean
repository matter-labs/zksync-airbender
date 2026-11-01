import Airbender.Proofs.Tables.ShiftPackedRowData

namespace Airbender.Verification.ShiftPackedReference
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def rowsCheck0 : Bool :=
  (List.range 1024).all fun row => numericRow 0 row == expectedRow 0 row

theorem rows_checked0 : rowsCheck0 = true := by decide +kernel

end Airbender.Verification.ShiftPackedReference
