import Slop.Blake2Round.Setup.Spec

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- Kernel check of the blocks of column 5 that start in rows [0, 1073741824). -/
theorem col5_walk : walk col5Spec 0 1073741824 col5Longs 0 blake2RoundSetup_col5 = true := by
  decide +kernel

end Airbender.Blake2Round.SetupProofs
