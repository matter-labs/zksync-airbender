import Airbender.Review.Helpers.Tables.NativeSrlHighData
import Airbender.Review.Helpers.Tables.SrlHigh

namespace Airbender.Verification.NativeSrlHigh

def Contains (query : Vector (ZMod mersenne31Modulus) 3) : Prop :=
  ∃ i : Fin data.length, query.push 51 = data.row i

end Airbender.Verification.NativeSrlHigh
