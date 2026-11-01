import Airbender.Proofs.Blake2G.Xor7PackedCapture

namespace Airbender.Blake2G.Proofs.Xor7PackedCapture
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : PackedXor7Checks.check 0 blocks = true := by decide +kernel

end Airbender.Blake2G.Proofs.Xor7PackedCapture
