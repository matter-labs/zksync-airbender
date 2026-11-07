import Airbender.Proofs.Tables.ShiftPackedEncoding.Column2Requests
import Airbender.Proofs.Tables.ShiftPackedRows

namespace Airbender.Verification.ShiftPackedEncoding.Lane2
open Airbender.Setup.Proofs.PackedWordColumn
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem requests_checked : checkRequests (ShiftPackedReference.checkSpan 2) requests = true := by
  decide +kernel

end Airbender.Verification.ShiftPackedEncoding.Lane2
