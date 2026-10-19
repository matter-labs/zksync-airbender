import Airbender.Proofs.Tables.SignFillHighPart0
import Airbender.Proofs.Tables.SignFillHighPart1
import Airbender.Proofs.Tables.SignFillHighPart2
import Airbender.Proofs.Tables.SignFillHighPart3

namespace Airbender.Verification.ShiftScalarProofs
open NativeShiftScalars
set_option warningAsError true
set_option Elab.async false

theorem sign_high (i : Fin 2097152) :
    dataSignFill.columns[2].get? i.val = some (signFillHigh i.val) := by
  have chunks : i.val / 32768 < 64 := by have := i.isLt; omega
  by_cases first : i.val / 32768 < 16
  · exact sign_high_part0 i (by omega) first
  by_cases second : i.val / 32768 < 32
  · exact sign_high_part1 i (by omega) second
  by_cases third : i.val / 32768 < 48
  · exact sign_high_part2 i (by omega) third
  exact sign_high_part3 i (by omega) chunks

end Airbender.Verification.ShiftScalarProofs
