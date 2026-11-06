import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 6 that start in rows [239872, 359680)
    (119808 rows checked one by one). -/
theorem col6_part2 : walkUpTo 65536 col6Spec 239872 359680 col6Longs 0 chi5Setup_col6 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
