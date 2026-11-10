import Airbender.Data.Setup.UnifiedReduced.Native.ZeroData
import Airbender.Data.Setup.UnifiedReduced.Native.ByteSignData
import Airbender.Data.Setup.UnifiedReduced.Native.XorData
import Airbender.Data.Setup.UnifiedReduced.Native.OrData
import Airbender.Data.Setup.UnifiedReduced.Native.AndData
import Airbender.Data.Setup.UnifiedReduced.Native.TruncationData
import Airbender.Data.Setup.UnifiedReduced.Native.ShiftData
import Airbender.Data.Setup.UnifiedReduced.Native.RegisterZeroData
import Airbender.Data.Setup.UnifiedReduced.Native.SignData
import Airbender.Data.Setup.UnifiedReduced.Native.CleanupData
import Airbender.Data.Setup.UnifiedReduced.Native.ConditionalData
import Airbender.Data.Setup.UnifiedReduced.Native.Rotate16Data
import Airbender.Data.Setup.UnifiedReduced.Native.Rotate12Data
import Airbender.Data.Setup.UnifiedReduced.Native.Rotate8Data
import Airbender.Data.Setup.UnifiedReduced.Native.Rotate7Data

namespace Airbender.UnifiedReduced.Setup

def nativeFixedData (kind : Fin 15) : Airbender.Setup.TableData 10 :=
  #v[nativeZeroData, nativeByteSignData, nativeXorData, nativeOrData, nativeAndData, nativeTruncationData, nativeShiftData, nativeRegisterZeroData, nativeSignData, nativeCleanupData, nativeConditionalData, nativeRotate16Data, nativeRotate12Data, nativeRotate8Data, nativeRotate7Data][kind]
def nativeFixedRegion (kind : Fin 15) : Airbender.Setup.Region :=
  #v[nativeZeroDataRegion, nativeByteSignDataRegion, nativeXorDataRegion, nativeOrDataRegion, nativeAndDataRegion, nativeTruncationDataRegion, nativeShiftDataRegion, nativeRegisterZeroDataRegion, nativeSignDataRegion, nativeCleanupDataRegion, nativeConditionalDataRegion, nativeRotate16DataRegion, nativeRotate12DataRegion, nativeRotate8DataRegion, nativeRotate7DataRegion][kind]
def nativeFixedRow (kind : Fin 15) (index : Nat) : Vector Nat 10 :=
  (nativeFixedData kind).columns.map fun column => (column.get? index).getD 0

end Airbender.UnifiedReduced.Setup
