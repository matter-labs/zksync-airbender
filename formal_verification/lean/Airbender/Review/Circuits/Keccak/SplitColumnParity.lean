import Airbender.Import.Embed

namespace Airbender.Keccak.Split.ColumnParity
set_option maxRecDepth 16384

/- The exact no-cache compiled column-parity circuit, including all 22 native
fixed-table queries and its delegation memory/timestamp metadata. Setup rows
and proof of worker behavior are separate obligations. -/
import_clean importedConstraints from
  "../../cs/compiled_circuits/keccak_column_parity_layout_no_caches_gkr.json"
  keccak_column_parity_lookups delegation_metadata

def clockConstraints {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 8)) : List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ColumnParity
