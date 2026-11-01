import Airbender.Proofs.Keccak.ChiPackedCertificate

namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem chi_output_checks :
    checkBlocks (fun n => (n % 256 ^^^ 255) &&& (n / 256)) 0
      chiData.columns[2].blocks.toList = true := by
  rw [← ChiPackedCapture.source_binding]
  exact PackedByteTableChecks.check_sound .chi 0 ChiPackedCapture.blocks ChiPackedCapture.checked

end Airbender.Keccak.Proofs
