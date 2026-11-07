import Airbender.Proofs.Tables.ShiftXorPackedCertificate
import Airbender.Proofs.Blake2G.Xor8Certificate

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem xor_outputs :
    checkBlocks (fun n => n / 256 ^^^ n % 256) 0
      byteXorData.columns[2].blocks.toList = true := by
  rw [← XorPackedCapture.source_binding]
  exact PackedByteTableChecks.check_sound .bitXor 0 XorPackedCapture.blocks XorPackedCapture.checked

end Airbender.Verification.ShiftCertificate
