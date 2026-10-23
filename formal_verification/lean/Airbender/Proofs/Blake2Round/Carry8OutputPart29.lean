import Airbender.Proofs.Blake2Round.Carry8OutputCertificate

namespace Airbender.Blake2Round.Proofs.Carry8Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem output_part29 :
    checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart29
      carry8ColumnBlocks29.toList = true :=
  output_parts.2.2.2.1.2

end Airbender.Blake2Round.Proofs.Carry8Certificate
