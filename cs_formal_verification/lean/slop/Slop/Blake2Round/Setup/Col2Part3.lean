import Slop.Blake2Round.Setup.Spec

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- Kernel check of the blocks of column 2 that start in rows [212992, 344064). -/
theorem col2_part3 : walk col2Spec 212992 344064 col2Longs 0 blake2RoundSetup_col2 = true := by
  decide +kernel

end Airbender.Blake2Round.SetupProofs
