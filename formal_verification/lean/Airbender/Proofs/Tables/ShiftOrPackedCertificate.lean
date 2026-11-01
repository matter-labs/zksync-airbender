import Airbender.Proofs.Tables.ShiftOrPackedCapture

namespace Airbender.Verification.ShiftCertificate.OrPackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedByteTableChecks.check .bitOr 0 blocks = true := by decide +kernel

end Airbender.Verification.ShiftCertificate.OrPackedCapture
