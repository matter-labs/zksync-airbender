import Slop.Blake2Round.Setup.Spec

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- Kernel check of the blocks of column 1 that start in rows [0, 1073741824). -/
theorem col1_walk : walk col1Spec 0 1073741824 col1Longs 0 blake2RoundSetup_col1 = true := by
  decide +kernel

end Airbender.Blake2Round.SetupProofs
