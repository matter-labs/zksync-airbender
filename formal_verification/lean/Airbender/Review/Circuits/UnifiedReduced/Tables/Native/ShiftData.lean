import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn0
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn1
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn2
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn3
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn4
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn5
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn6
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn7
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn8
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn9

namespace Airbender.UnifiedReduced.Setup

def nativeShiftData : Airbender.Setup.TableData 10 :=
  ⟨nativeShiftColumn0Region.length, 0,
    #v[nativeShiftColumn0, nativeShiftColumn1, nativeShiftColumn2, nativeShiftColumn3,
      nativeShiftColumn4, nativeShiftColumn5, nativeShiftColumn6, nativeShiftColumn7,
      nativeShiftColumn8, nativeShiftColumn9]⟩
def nativeShiftDataRegion : Airbender.Setup.Region := nativeShiftColumn0Region
def nativeShiftDataSourceBytes : String := nativeUnifiedSourceBytes

end Airbender.UnifiedReduced.Setup
