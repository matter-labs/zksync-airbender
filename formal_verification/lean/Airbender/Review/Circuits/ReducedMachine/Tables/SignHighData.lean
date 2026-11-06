import Airbender.Import.ReducedSetupEmbed

namespace Airbender.ReducedMachine.SignHigh

import_native_reduced_sign_high data from "artifacts/setup/reduced-sign-high-native.json"

/-- Membership in this actual exported region, not in the entire pooled setup. -/
def Contains (query : Vector (ZMod mersenne31Modulus) 4) : Prop :=
  ∃ i : Fin data.length, query = data.row i

end Airbender.ReducedMachine.SignHigh
