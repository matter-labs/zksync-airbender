import Slop.Blake2Round.Setup.Spec

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- Kernel check of the blocks of column 2 that start in rows [65536, 81920). -/
theorem col2_part1 : walk col2Spec 65536 81920 col2Longs 0 blake2RoundSetup_col2 = true := by
  decide +kernel

end Airbender.Blake2Round.SetupProofs
