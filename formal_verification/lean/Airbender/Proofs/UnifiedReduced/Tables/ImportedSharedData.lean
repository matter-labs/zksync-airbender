import Airbender.Data.Setup.UnifiedReduced.Native.RegisterZeroData
import Airbender.Data.Setup.UnifiedReduced.Native.CleanupData
import Airbender.Data.Setup.UnifiedReduced.Native.ByteSignData
import Airbender.Data.Setup.UnifiedReduced.Native.SignData
import Airbender.Data.Setup.UnifiedReduced.Native.TruncationData
import Airbender.Review.Helpers.Tables.PairData
import Airbender.Data.Tables.Shift.SignData
import Airbender.Data.Tables.Shift.TruncateData

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

/-- Independently imported complete physical columns for the shared native regions. -/
theorem imported_register_zero_data : nativeRegisterZeroData = regZeroData := rfl
theorem imported_cleanup_data : nativeCleanupData = jumpCleanupData := rfl

end Airbender.UnifiedReduced.Setup.Proofs
