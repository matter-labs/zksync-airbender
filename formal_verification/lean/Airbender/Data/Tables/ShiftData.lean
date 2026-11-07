import Airbender.Data.Tables.Shift.ZeroData
import Airbender.Data.Tables.Shift.SignData
import Airbender.Data.Tables.Shift.XorData
import Airbender.Data.Tables.Shift.OrData
import Airbender.Data.Tables.Shift.AndData
import Airbender.Data.Tables.Shift.TruncateData
import Airbender.Data.Tables.Shift.ShiftData

namespace Airbender.Verification

def shiftData (kind : Fin 7) : Setup.TableData 10 :=
  #v[byteZeroData, byteSignData, byteXorData, byteOrData, byteAndData,
    byteTruncateData, byteShiftData][kind]

def shiftRegion (kind : Fin 7) : Setup.Region :=
  #v[byteZeroDataRegion, byteSignDataRegion, byteXorDataRegion, byteOrDataRegion,
    byteAndDataRegion, byteTruncateDataRegion, byteShiftDataRegion][kind]

def shiftRegionRow (kind : Fin 7) (index : Nat) : Vector Nat 10 :=
  (shiftData kind).columns.map fun column => (column.get? index).getD 0

end Airbender.Verification
