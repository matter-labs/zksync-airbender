import Airbender.Proofs.Blake2G.Xor7PackedCertificate

namespace Airbender.Blake2G.Proofs.XorCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem output7 : checkBlocks (fun n => n / 128 ^^^ n % 128) 0
    (xor7Data.columns[2]'(by omega)).blocks.toList = true := by
  rw [← Xor7PackedCapture.source_binding]
  exact PackedXor7Checks.check_sound 0 Xor7PackedCapture.blocks Xor7PackedCapture.checked

end Airbender.Blake2G.Proofs.XorCertificate
