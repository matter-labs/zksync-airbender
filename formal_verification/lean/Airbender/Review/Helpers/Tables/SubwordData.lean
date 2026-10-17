import Airbender.Review.Helpers.Tables.Subword.ZeroData
import Airbender.Review.Helpers.Tables.Subword.StorePlaceData
import Airbender.Review.Helpers.Tables.Subword.StoreClearData
import Airbender.Review.Helpers.Tables.Subword.LoadHalfData
import Airbender.Review.Helpers.Tables.Subword.LoadByteData

namespace Airbender.Verification

def subwordFixedData (kind : Fin 4) : Setup.TableData 9 :=
  #v[storePlaceData, storeClearData, loadHalfData, loadByteData][kind]
def subwordFixedRegion (kind : Fin 4) : Setup.Region :=
  #v[storePlaceDataRegion, storeClearDataRegion, loadHalfDataRegion, loadByteDataRegion][kind]
def subwordFixedRow (kind : Fin 4) (index : Nat) : Vector Nat 9 :=
  (subwordFixedData kind).columns.map fun column => (column.get? index).getD 0

end Airbender.Verification
