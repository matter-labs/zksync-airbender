import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Data.Setup.Blake2G.XorData
import Airbender.Proofs.Tables.LiteralColumnParts

namespace Airbender.Blake2G.Proofs.Xor9Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

literal_column_parts xor9Column from (xor9Data.columns[2]) depth 6

end Airbender.Blake2G.Proofs.Xor9Certificate
