import Slop.KeccakSplit.Setup.ColumnParity.Shapes

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 3 that start in rows [0, 1073741824)
    (243 rows checked one by one). -/
theorem col3_walk : walkUpTo 512 col3Spec 0 1073741824 col3Longs 0 columnParitySetup_col3 = true := by
  decide +kernel

end Airbender.Keccak.Split.ColumnParity.SetupProofs
