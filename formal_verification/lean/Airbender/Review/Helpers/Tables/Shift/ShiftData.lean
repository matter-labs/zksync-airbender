import Airbender.Review.Helpers.Tables.Shift.Column0
import Airbender.Review.Helpers.Tables.Shift.Column1
import Airbender.Review.Helpers.Tables.Shift.Column2
import Airbender.Review.Helpers.Tables.Shift.Column3
import Airbender.Review.Helpers.Tables.Shift.Column4
import Airbender.Review.Helpers.Tables.Shift.Column5
import Airbender.Review.Helpers.Tables.Shift.Column6
import Airbender.Review.Helpers.Tables.Shift.Column7
import Airbender.Review.Helpers.Tables.Shift.Column8
import Airbender.Review.Helpers.Tables.Shift.Column9

namespace Airbender.Verification

def byteShiftData : Setup.TableData 10 :=
  ⟨byteShiftColumn0Region.length, 0,
    #v[byteShiftColumn0, byteShiftColumn1, byteShiftColumn2, byteShiftColumn3,
      byteShiftColumn4, byteShiftColumn5, byteShiftColumn6, byteShiftColumn7,
      byteShiftColumn8, byteShiftColumn9]⟩
def byteShiftDataRegion : Setup.Region := byteShiftColumn0Region
def byteShiftDataSourceBytes : String := nativeShiftSourceBytes

end Airbender.Verification
