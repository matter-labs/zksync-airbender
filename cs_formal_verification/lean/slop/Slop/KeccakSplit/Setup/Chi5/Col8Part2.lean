import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 8 that start in rows [757760, 876544)
    (118784 rows checked one by one). -/
theorem col8_part2 : walkUpTo 65536 col8Spec 757760 876544 col8Longs 0 chi5Setup_col8 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
