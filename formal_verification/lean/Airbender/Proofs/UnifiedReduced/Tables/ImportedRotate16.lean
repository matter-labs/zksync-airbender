import Airbender.Data.Setup.UnifiedReduced.Native.Rotate16Data
import Airbender.Data.Tables.Shift.XorData

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

/-- The independently imported nonzero byte of ROR16 is the native XOR column. -/
theorem imported_rotate16_xor : nativeRotate16Data.columns[4] = byteXorData.columns[2] := by
  dsimp only [nativeRotate16Data, byteXorData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]

end Airbender.UnifiedReduced.Setup.Proofs
