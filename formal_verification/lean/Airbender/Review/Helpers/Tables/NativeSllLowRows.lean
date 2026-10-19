import Airbender.Review.Helpers.Tables.NativeSllLowData
import Airbender.Review.Helpers.Tables.SllLow

namespace Airbender.Verification.NativeSllLow

def Contains (query : Vector (ZMod mersenne31Modulus) 3) : Prop :=
  ∃ i : Fin data.length, query.push 48 = data.row i

end Airbender.Verification.NativeSllLow
