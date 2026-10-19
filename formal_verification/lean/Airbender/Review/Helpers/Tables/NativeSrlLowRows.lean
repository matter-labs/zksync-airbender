import Airbender.Review.Helpers.Tables.NativeSrlLowData
import Airbender.Review.Helpers.Tables.SrlLow

namespace Airbender.Verification.NativeSrlLow

def Contains (query : Vector (ZMod mersenne31Modulus) 3) : Prop :=
  ∃ i : Fin data.length, query.push 50 = data.row i

end Airbender.Verification.NativeSrlLow
