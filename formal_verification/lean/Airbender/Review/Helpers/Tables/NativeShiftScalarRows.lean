import Airbender.Review.Helpers.Tables.NativeShiftScalarData
import Airbender.Review.Helpers.Tables.ShiftScalars

namespace Airbender.Verification.NativeShiftScalars

def data : ShiftScalarKind → Setup.TableData 4
  | .truncate => dataTruncate | .signFill => dataSignFill | .range => dataRange

def row (kind : ShiftScalarKind) (i : Fin kind.length) : Vector Nat 4 :=
  (data kind).columns.map fun column => (column.get? i.val).getD 0

def Contains (kind : ShiftScalarKind) (query : Vector (ZMod mersenne31Modulus) 3) : Prop :=
  ∃ i, query.push (kind.tag : ZMod mersenne31Modulus) = (row kind i).map Nat.cast

end Airbender.Verification.NativeShiftScalars
