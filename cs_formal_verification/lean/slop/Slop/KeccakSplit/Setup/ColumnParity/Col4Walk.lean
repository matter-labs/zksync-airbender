import Slop.KeccakSplit.Setup.ColumnParity.Shapes

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 4 that start in rows [0, 1073741824)
    (121 rows checked one by one). -/
theorem col4_walk : walkUpTo 512 col4Spec 0 1073741824 col4Longs 0 columnParitySetup_col4 = true := by
  decide +kernel

end Airbender.Keccak.Split.ColumnParity.SetupProofs
