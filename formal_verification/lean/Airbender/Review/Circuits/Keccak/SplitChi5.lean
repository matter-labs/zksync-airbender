import Airbender.Import.Embed

namespace Airbender.Keccak.Split.Chi5
set_option maxRecDepth 16384

/- The exact no-cache compiled chi5 equations, all 17 fixed-table queries,
native timestamp queries and grouped memory-port descriptors. -/
import_clean importedConstraints from
  "../../cs/compiled_circuits/keccak_chi5_layout_no_caches_gkr.json"
  keccak_chi5_lookups split_delegation_timestamps

def clockConstraints {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 11)) : List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.Chi5
