import Airbender.Data.Tables.Shift.OrPackedPilot
import Airbender.Data.Tables.Shift.OrData
import Airbender.Proofs.Tables.PackedBitwise

namespace Airbender.Verification.PackedOrPilot
open Airbender.Setup.Proofs.PackedBitwise
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem ok : check .bitOr byteOrPackedPilot = true := by decide +kernel

/-- Every imported byte OR output follows from the checked packed rows. -/
theorem or_outputs_packed : Fact .bitOr byteOrPackedPilot := check_sound _ _ ok

/-- Both import paths use the same complete native setup artifact bytes. -/
theorem same_source_bytes :
    byteOrPackedPilotSourceBytes = byteOrDataSourceBytes := rfl

end Airbender.Verification.PackedOrPilot
