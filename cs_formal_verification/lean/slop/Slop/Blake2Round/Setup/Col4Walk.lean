import Slop.Blake2Round.Setup.Spec

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- Kernel check of the blocks of column 4 that start in rows [0, 1073741824). -/
theorem col4_walk : walk col4Spec 0 1073741824 col4Longs 0 blake2RoundSetup_col4 = true := by
  decide +kernel

end Airbender.Blake2Round.SetupProofs
