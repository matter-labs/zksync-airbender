import Slop.KeccakSplit.Setup.ColumnParity.Shapes

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 7 that start in rows [0, 1073741824)
    (244 rows checked one by one). -/
theorem col7_walk : walkUpTo 512 col7Spec 0 1073741824 col7Longs 0 columnParitySetup_col7 = true := by
  decide +kernel

end Airbender.Keccak.Split.ColumnParity.SetupProofs
