import Airbender.Import.Embed

namespace Airbender.Keccak.Split.ThetaRhoCached
set_option maxRecDepth 16384

/- The cached production variant of the native theta/rho circuit. The
grouped timestamp descriptor does not itself prove memory timing. -/
import_clean importedConstraints from
  "../../cs/compiled_circuits/keccak_theta_rho_layout_gkr.json"
  keccak_theta_rho_lookups split_delegation_timestamps

def clockConstraints {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 9)) : List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ThetaRhoCached
