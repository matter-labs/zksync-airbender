import Airbender.Import.Embed

namespace Airbender.Keccak.Split.Chi5Cached
set_option maxRecDepth 16384

/- The cached production variant of the native chi5 circuit. The grouped
timestamp descriptor does not itself prove memory timing. -/
import_clean importedConstraints from
  "../../cs/compiled_circuits/keccak_chi5_layout_gkr.json"
  keccak_chi5_lookups split_delegation_timestamps

def clockConstraints {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 11)) : List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.Chi5Cached
