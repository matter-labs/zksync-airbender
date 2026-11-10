import Airbender.Proofs.Blake2G.Xor9Certificate
import Airbender.Proofs.Blake2G.XorCertificateBase
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem output9 : checkBlocks (fun n => n / 512 ^^^ n % 512) 0
    (xor9Data.columns[2]'(by omega)).blocks.toList = true :=
  Xor9Certificate.output_checks

/-- Kernel certificates over all actual output blocks. Array/list identities
    and template getters are normalized before the bounded finite checks. -/
theorem imported_xor_output_checks (kind : Fin 5) :
    checkBlocks (fun n => n / 2 ^ (#v[8, 3, 4, 7, 9][kind]) ^^^
      n % 2 ^ (#v[8, 3, 4, 7, 9][kind])) 0
      (xorData kind).columns[2].blocks.toList = true := by
  fin_cases kind
  · exact XorCertificate.output8
  · exact XorCertificate.output3
  · exact XorCertificate.output4
  · exact XorCertificate.output7
  · exact output9

end Airbender.Blake2G.Proofs
