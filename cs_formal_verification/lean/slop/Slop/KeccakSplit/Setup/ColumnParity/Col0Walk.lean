import Slop.KeccakSplit.Setup.ColumnParity.Shapes

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 0 that start in rows [0, 1073741824)
    (516 rows checked one by one). -/
theorem col0_walk : walkUpTo 512 col0Spec 0 1073741824 col0Longs 0 columnParitySetup_col0 = true := by
  decide +kernel

end Airbender.Keccak.Split.ColumnParity.SetupProofs
