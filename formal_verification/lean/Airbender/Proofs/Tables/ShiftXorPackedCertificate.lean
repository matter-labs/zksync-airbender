import Airbender.Proofs.Tables.ShiftXorPackedCapture

namespace Airbender.Verification.ShiftCertificate.XorPackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedByteTableChecks.check .bitXor 0 blocks = true := by decide +kernel

end Airbender.Verification.ShiftCertificate.XorPackedCapture
