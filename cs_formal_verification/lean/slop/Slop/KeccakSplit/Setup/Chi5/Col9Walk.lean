import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 9 that start in rows [0, 1073741824)
    (4096 rows checked one by one). -/
theorem col9_walk : walkUpTo 512 col9Spec 0 1073741824 col9Longs 0 chi5Setup_col9 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
