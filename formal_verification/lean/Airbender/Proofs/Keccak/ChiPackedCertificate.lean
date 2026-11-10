import Airbender.Proofs.Keccak.ChiPackedCapture

namespace Airbender.Keccak.Proofs.ChiPackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedByteTableChecks.check .chi 0 blocks = true := by decide +kernel

end Airbender.Keccak.Proofs.ChiPackedCapture
