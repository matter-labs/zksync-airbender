import Airbender.Proofs.Tables.ShiftAndPackedCertificate

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true

theorem and_outputs :
    checkBlocks (fun n => n / 256 &&& n % 256) 0
      byteAndData.columns[2].blocks.toList = true :=
  ShiftPackedCertificate.and_outputs

end Airbender.Verification.ShiftCertificate
