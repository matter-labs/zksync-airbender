import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 7 that start in rows [237568, 356352)
    (118784 rows checked one by one). -/
theorem col7_part2 : walkUpTo 65536 col7Spec 237568 356352 col7Longs 0 chi5Setup_col7 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
