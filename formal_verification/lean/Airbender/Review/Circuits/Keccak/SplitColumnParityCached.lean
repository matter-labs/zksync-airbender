import Airbender.Import.Embed

namespace Airbender.Keccak.Split.ColumnParityCached
set_option maxRecDepth 16384

/- The cached production variant of the native column-parity circuit.
Its setup rows and worker behavior remain separate proof obligations. -/
import_clean importedConstraints from
  "../../cs/compiled_circuits/keccak_column_parity_layout_gkr.json"
  keccak_column_parity_lookups delegation_metadata

def clockConstraints {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 8)) : List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ColumnParityCached
