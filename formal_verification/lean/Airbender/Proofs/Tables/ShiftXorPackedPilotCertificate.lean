import Airbender.Data.Tables.Shift.XorPackedPilot
import Airbender.Data.Tables.Shift.XorData
import Airbender.Proofs.Tables.PackedBitwise

namespace Airbender.Verification.PackedXorPilot
open Airbender.Setup.Proofs.PackedBitwise
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem ok : check .bitXor byteXorPackedPilot = true := by decide +kernel

/-- Every imported byte XOR output follows from the checked packed rows. -/
theorem xor_outputs_packed : Fact .bitXor byteXorPackedPilot := check_sound _ _ ok

/-- Both import paths use the same complete native setup artifact bytes. -/
theorem same_source_bytes :
    byteXorPackedPilotSourceBytes = byteXorDataSourceBytes := rfl

end Airbender.Verification.PackedXorPilot
