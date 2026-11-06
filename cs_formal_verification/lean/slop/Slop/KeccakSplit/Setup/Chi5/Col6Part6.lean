import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 6 that start in rows [718016, 837632)
    (119616 rows checked one by one). -/
theorem col6_part6 : walkUpTo 65536 col6Spec 718016 837632 col6Longs 0 chi5Setup_col6 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
