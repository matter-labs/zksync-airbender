import Airbender.Data.Setup.UnifiedReduced.Native.XorData
import Airbender.Data.Setup.UnifiedReduced.Native.OrData
import Airbender.Data.Setup.UnifiedReduced.Native.AndData
import Airbender.Data.Tables.Shift.XorData
import Airbender.Data.Tables.Shift.OrData
import Airbender.Data.Tables.Shift.AndData
import Mathlib.Tactic.FinCases

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

def wideData (kind : Fin 3) : Airbender.Setup.TableData 10 :=
  #v[nativeXorData, nativeOrData, nativeAndData][kind]
def ordinaryData (kind : Fin 3) : Airbender.Setup.TableData 10 :=
  #v[byteXorData, byteOrData, byteAndData][kind]

/-- The independently imported ordinary and wide data agree before the native tag. -/
theorem wide_columns (kind : Fin 3) (lane : Fin 9) (notSecondKey : lane.val ≠ 1) :
    (wideData kind).columns[lane.val] = (ordinaryData kind).columns[lane.val] := by
  fin_cases kind <;> fin_cases lane <;> first | contradiction | rfl

end Airbender.UnifiedReduced.Setup.Proofs
