import Slop.KeccakSplit.Setup.ColumnParity.Shapes

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 5 that start in rows [135532, 205524)
    (69992 rows checked one by one). -/
theorem col5_part1 : walkUpTo 512 col5Spec 135532 205524 col5Longs 0 columnParitySetup_col5 = true := by
  decide +kernel

end Airbender.Keccak.Split.ColumnParity.SetupProofs
