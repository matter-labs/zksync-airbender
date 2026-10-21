import Airbender.Review.Circuits.Blake2Round.Tables.XorData
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.LiteralColumnParts

namespace Airbender.Blake2Round.Proofs.Carry8Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

literal_column_parts carry8Column from (xor8CarryData.columns[3]) depth 5

end Airbender.Blake2Round.Proofs.Carry8Certificate
