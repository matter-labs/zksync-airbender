import Airbender.Proofs.Tables.ShiftOrPackedCertificate

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem or_outputs :
    checkBlocks (fun n => n / 256 ||| n % 256) 0
      byteOrData.columns[2].blocks.toList = true := by
  rw [← OrPackedCapture.source_binding]
  exact PackedByteTableChecks.check_sound .bitOr 0 OrPackedCapture.blocks OrPackedCapture.checked

end Airbender.Verification.ShiftCertificate
