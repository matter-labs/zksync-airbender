import Airbender.Data.Setup.UnifiedReduced.Native.Rotate8Data
import Airbender.Proofs.Blake2G.Xor8Certificate
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

/- Retain the bound proof in the original public theorem type. -/
set_option linter.auxLemma false in
theorem imported_rotate8_output._proof_1 : (¬ (5 < 10)) → False := by
  decide +kernel

/- Bind the complete independently imported output column. -/
numeric_data_binding rotate8_output_binding : nativeRotate8Data.columns[5].blocks =
  (Airbender.Blake2G.xor8Data.columns[2]'(by decide)).blocks

theorem imported_rotate8_output : checkBlocks (fun n => n / 256 ^^^ n % 256) 0
    nativeRotate8Data.columns[5].blocks.toList = true := by
  rw [rotate8_output_binding]
  exact Airbender.Blake2G.Proofs.XorCertificate.output8


end Airbender.UnifiedReduced.Setup.Proofs
