import Airbender.Proofs.UnifiedReduced.Tables.ReferenceRows
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ConditionalData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/-- All seven-bit keys, including invalid combinations, in native ID 51. -/
theorem imported_conditional_row (index : Fin 128) :
    nativeConditionalData.columns.map (fun column => (column.get? index.val).getD 0) =
      (#v[index.val, conditionalValue (conditionalKey index.val),
        0, 0, 0, 0, 0, 0, 0, 51] : Vector Nat 10) := by
  revert index
  decide +kernel

end Airbender.UnifiedReduced.Setup.Proofs
