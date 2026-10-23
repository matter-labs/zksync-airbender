import Airbender.Proofs.Keccak.ChiCertificate
import Airbender.Review.Circuits.Keccak.Tables.FixedData
import Airbender.Review.Circuits.Keccak.Tables.Operations
import Airbender.Proofs.Blake2G.Xor8Certificate

namespace Airbender.Keccak.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem xor_output_checks :
    checkBlocks (fun n => n / 256 ^^^ n % 256) 0 xorData.columns[2].blocks.toList = true := by
  exact Blake2G.Proofs.XorCertificate.output8


end Airbender.Keccak.Proofs
