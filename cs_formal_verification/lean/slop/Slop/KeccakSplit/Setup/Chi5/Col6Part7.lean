import Slop.KeccakSplit.Setup.Chi5.Shapes

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxRecDepth 400000

/-- Kernel check of the blocks of column 6 that start in rows [837632, 956416)
    (118784 rows checked one by one). -/
theorem col6_part7 : walkUpTo 65536 col6Spec 837632 956416 col6Longs 0 chi5Setup_col6 = true := by
  decide +kernel

end Airbender.Keccak.Split.Chi5.SetupProofs
