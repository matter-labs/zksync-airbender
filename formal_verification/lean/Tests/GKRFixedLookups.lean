import GKRProtocol.FixedSetupNative.JumpBranchMembership
import GKRProtocol.FixedSetupNative.MulDivMembership

namespace Tests.GKRFixedLookups
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem rejects_shifted_sign_region :
    FixedSetupNative.JumpBranch.nativeSetup.imported.data.columns[0].get? (196609 + 7) ≠
      Verification.signData.columns[0].get? 7 := by decide +kernel

theorem rejects_cleanup_column_swap :
    FixedSetupNative.JumpBranch.nativeSetup.imported.data.columns[1].get? (131072 + 7) ≠
      Verification.jumpCleanupData.columns[2].get? 7 := by decide +kernel

theorem decoder_region_has_distinct_tag :
    FixedSetupNative.JumpBranch.nativeSetup.value ⟨4456448, by decide⟩ (.generic 9) = 46 := by
  decide +kernel

theorem native_range13_last_value :
    FixedSetupNative.MulDiv.nativeSetup.value ⟨196608 + 8191, by decide⟩ (.generic 0) = 8191 := by
  decide +kernel

end Tests.GKRFixedLookups
