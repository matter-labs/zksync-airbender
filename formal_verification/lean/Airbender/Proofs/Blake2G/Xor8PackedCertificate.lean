import Airbender.Proofs.Blake2G.Xor8PackedCapture

namespace Airbender.Blake2G.Proofs.Xor8PackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedByteTableChecks.check .bitXor 0 blocks = true := by decide +kernel

end Airbender.Blake2G.Proofs.Xor8PackedCapture
