import Airbender.Proofs.Tables.ShiftPackedRowData

namespace Airbender.Verification.ShiftPackedReference
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def rowsCheck3 : Bool :=
  (List.range 1024).all fun row => numericRow 3 row == expectedRow 3 row

theorem rows_checked3 : rowsCheck3 = true := by decide +kernel

end Airbender.Verification.ShiftPackedReference
