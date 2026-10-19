import Airbender.Review.Helpers.Tables.NativeBinaryData
import Airbender.Review.Helpers.Tables.Binary

namespace Airbender.Verification.NativeBinary

/-- Select actual stored columns; no lookup recipe is inserted by the importer. -/
def columns : BinaryKind → Vector Setup.Column 4
  | .xor => dataXor.columns | .or => dataOr.columns | .and => dataAnd.columns

def row (kind : BinaryKind) (i : Fin 65536) : Vector Nat 4 :=
  (columns kind).map fun column => (column.get? i.val).getD 0

def Contains (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3) : Prop :=
  ∃ i, query.push (kind.tag : ZMod mersenne31Modulus) = (row kind i).map Nat.cast

end Airbender.Verification.NativeBinary
