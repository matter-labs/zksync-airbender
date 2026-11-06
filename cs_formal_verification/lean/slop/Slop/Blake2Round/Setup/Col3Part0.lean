import Slop.Blake2Round.Setup.Spec

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- Kernel check of the blocks of column 3 that start in rows [0, 442368). -/
theorem col3_part0 : walk col3Spec 0 442368 col3Longs 0 blake2RoundSetup_col3 = true := by
  decide +kernel

end Airbender.Blake2Round.SetupProofs
