import Airbender.Data.Tables.Subword.ROMHalfData
import Airbender.Data.Tables.Subword.ROMByteData

namespace Airbender.Verification

def subwordROMData (byte : Bool) : Setup.TableData 9 :=
  if byte then subwordROMByteData else subwordROMHalfData

def subwordROMRegion (byte : Bool) : Setup.Region :=
  if byte then subwordROMByteDataRegion else subwordROMHalfDataRegion

def subwordROMRow (byte : Bool) (index : Nat) : Vector Nat 9 :=
  (subwordROMData byte).columns.map fun column => (column.get? index).getD 0

end Airbender.Verification
