import Airbender.Data.Setup.UnifiedReduced.Native.XorPackedPilot
import Airbender.Data.Setup.UnifiedReduced.Native.Source
import Airbender.Proofs.Tables.PackedBitwise

namespace Airbender.UnifiedReduced.Setup.PackedPilot
open Airbender.Setup.Proofs.PackedBitwise
set_option warningAsError true
set_option maxRecDepth 131072
set_option maxHeartbeats 0

/-- Capture-specific Boolean check; semantic soundness is proved once in
`PackedBitwise.check_sound`. -/
theorem ok : check .bitXor nativeXorPackedPilot = true := by decide +kernel

/-- Every one of the 65,536 native XOR8 output bytes has the expected value.
The existing Block/shard certificates remain in use until consumers migrate. -/
theorem xor_outputs_packed : Fact .bitXor nativeXorPackedPilot :=
  check_sound .bitXor nativeXorPackedPilot ok

/-- The compact pilot and the original unified setup importer read the same
complete JSON artifact bytes. Parsing and slicing remain importer trust. -/
theorem same_source_bytes :
    nativeXorPackedPilotSourceBytes = nativeUnifiedSourceBytes := rfl

end Airbender.UnifiedReduced.Setup.PackedPilot
