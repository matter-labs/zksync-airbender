import Slop.Blake2Round.Setup.Spec

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- Kernel check of the blocks of column 0 that start in rows [0, 1073741824). -/
theorem col0_walk : walk col0Spec 0 1073741824 col0Longs 0 blake2RoundSetup_col0 = true := by
  decide +kernel

end Airbender.Blake2Round.SetupProofs
