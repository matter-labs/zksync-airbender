import Airbender.Data.Setup.UnifiedReduced.Native.ShiftColumn3
import Airbender.Data.Tables.Shift.Column3
import Airbender.Proofs.Tables.ColumnAgreement

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem shift_column3_agreement :
    blocksAgree nativeShiftColumn3.blocks.toList byteShiftColumn3.blocks.toList = true := by
  decide +kernel

end Airbender.UnifiedReduced.Setup.Proofs
