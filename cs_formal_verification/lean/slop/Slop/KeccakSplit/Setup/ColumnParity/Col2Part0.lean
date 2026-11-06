import Slop.KeccakSplit.Setup.ColumnParity.Shapes

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 2 that start in rows [0, 65780)
    (65780 rows checked one by one). -/
theorem col2_part0 : walkUpTo 65536 col2Spec 0 65780 col2Longs 0 columnParitySetup_col2 = true := by
  decide +kernel

end Airbender.Keccak.Split.ColumnParity.SetupProofs
