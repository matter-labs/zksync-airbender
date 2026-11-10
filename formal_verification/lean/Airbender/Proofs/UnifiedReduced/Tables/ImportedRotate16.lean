import Airbender.Data.Setup.UnifiedReduced.Native.Rotate16Data
import Airbender.Data.Tables.Shift.XorData
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

/- Retain the bounds in the original public theorem type. -/
set_option linter.auxLemma false in
theorem imported_rotate16_xor._proof_1 : (¬ (4 < 10)) → False := by decide +kernel

set_option linter.auxLemma false in
theorem imported_rotate16_xor._proof_2 : (¬ (2 < 10)) → False := by decide +kernel

/- The independently imported nonzero byte of ROR16 is the native XOR column. -/
numeric_data_binding imported_rotate16_xor : nativeRotate16Data.columns[4] = byteXorData.columns[2]

end Airbender.UnifiedReduced.Setup.Proofs
