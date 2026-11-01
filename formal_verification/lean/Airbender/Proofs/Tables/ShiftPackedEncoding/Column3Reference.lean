import Airbender.Proofs.Tables.ShiftPackedEncoding.Column3Requests
import Airbender.Proofs.Tables.ShiftPackedRows

namespace Airbender.Verification.ShiftPackedEncoding.Lane3
open Airbender.Setup.Proofs.PackedWordColumn
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem requests_checked : checkRequests (ShiftPackedReference.checkSpan 3) requests = true := by
  decide +kernel

end Airbender.Verification.ShiftPackedEncoding.Lane3
