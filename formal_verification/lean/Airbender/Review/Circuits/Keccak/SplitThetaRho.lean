import Airbender.Import.Embed

namespace Airbender.Keccak.Split.ThetaRho
set_option maxRecDepth 16384

/- The exact no-cache compiled theta/rho equations, all 50 fixed-table queries,
native timestamp queries and grouped memory-port descriptors. -/
import_clean importedConstraints from
  "../../cs/compiled_circuits/keccak_theta_rho_layout_no_caches_gkr.json"
  keccak_theta_rho_lookups split_delegation_timestamps

def clockConstraints {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 9)) : List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ThetaRho
