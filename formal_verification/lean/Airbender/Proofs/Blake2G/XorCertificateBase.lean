import Airbender.Proofs.Blake2G.Xor7Certificate
import Airbender.Proofs.Blake2G.Xor8Certificate
import Airbender.Data.Setup.Blake2G.XorData
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs.XorCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 131072

theorem output3 : checkBlocks (fun n => n / 8 ^^^ n % 8) 0
    (xor3Data.columns[2]'(by omega)).blocks.toList = true := by decide +kernel

theorem output4 : checkBlocks (fun n => n / 16 ^^^ n % 16) 0
    (xor4Data.columns[2]'(by omega)).blocks.toList = true := by decide +kernel

end Airbender.Blake2G.Proofs.XorCertificate
