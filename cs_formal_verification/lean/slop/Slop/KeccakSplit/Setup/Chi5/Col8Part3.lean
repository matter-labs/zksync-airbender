import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 8 that start in rows [876544, 995328)
    (118784 rows checked one by one). -/
theorem col8_part3 : walkUpTo 65536 col8Spec 876544 995328 col8Longs 0 chi5Setup_col8 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
