import Airbender.Proofs.Blake2G.Xor8PackedCertificate

namespace Airbender.Blake2G.Proofs.XorCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem output8 :
    checkBlocks (fun n => n / 256 ^^^ n % 256) 0
      (xor8Data.columns[2]'(by omega)).blocks.toList = true := by
  rw [← Xor8PackedCapture.source_binding]
  exact PackedByteTableChecks.check_sound .bitXor 0 Xor8PackedCapture.blocks Xor8PackedCapture.checked

end Airbender.Blake2G.Proofs.XorCertificate
