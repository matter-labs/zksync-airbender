import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ZeroData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ByteSignData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.XorData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.OrData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.AndData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.TruncationData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.RegisterZeroData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.SignData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.CleanupData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ConditionalData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.Rotate16Data
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.Rotate12Data
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.Rotate8Data
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.Rotate7Data

namespace Airbender.UnifiedReduced.Setup

def nativeFixedData (kind : Fin 15) : Airbender.Setup.TableData 10 :=
  #v[nativeZeroData, nativeByteSignData, nativeXorData, nativeOrData, nativeAndData, nativeTruncationData, nativeShiftData, nativeRegisterZeroData, nativeSignData, nativeCleanupData, nativeConditionalData, nativeRotate16Data, nativeRotate12Data, nativeRotate8Data, nativeRotate7Data][kind]
def nativeFixedRegion (kind : Fin 15) : Airbender.Setup.Region :=
  #v[nativeZeroDataRegion, nativeByteSignDataRegion, nativeXorDataRegion, nativeOrDataRegion, nativeAndDataRegion, nativeTruncationDataRegion, nativeShiftDataRegion, nativeRegisterZeroDataRegion, nativeSignDataRegion, nativeCleanupDataRegion, nativeConditionalDataRegion, nativeRotate16DataRegion, nativeRotate12DataRegion, nativeRotate8DataRegion, nativeRotate7DataRegion][kind]
def nativeFixedRow (kind : Fin 15) (index : Nat) : Vector Nat 10 :=
  (nativeFixedData kind).columns.map fun column => (column.get? index).getD 0

end Airbender.UnifiedReduced.Setup
