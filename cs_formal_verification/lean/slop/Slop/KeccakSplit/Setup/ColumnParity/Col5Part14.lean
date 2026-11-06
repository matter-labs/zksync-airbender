import Slop.KeccakSplit.Setup.ColumnParity.Shapes

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 5 that start in rows [1045524, 1073741824)
    (68832 rows checked one by one). -/
theorem col5_part14 : walkUpTo 512 col5Spec 1045524 1073741824 col5Longs 0 columnParitySetup_col5 = true := by
  decide +kernel

end Airbender.Keccak.Split.ColumnParity.SetupProofs
