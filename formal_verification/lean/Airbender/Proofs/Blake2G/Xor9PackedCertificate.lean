import Airbender.Proofs.Blake2G.Xor9PackedCapture

namespace Airbender.Blake2G.Proofs.Xor9PackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedXor9Checks.checkRequests requests = true := by decide +kernel

end Airbender.Blake2G.Proofs.Xor9PackedCapture
