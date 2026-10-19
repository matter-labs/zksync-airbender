import Airbender.Review.Helpers.Tables.NativeSllHighData
import Airbender.Review.Helpers.Tables.SllHigh

namespace Airbender.Verification.NativeSllHigh

def Contains (query : Vector (ZMod mersenne31Modulus) 3) : Prop :=
  ∃ i : Fin data.length, query.push 49 = data.row i

end Airbender.Verification.NativeSllHigh
