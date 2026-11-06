import Human.Import.Embed

namespace Airbender.Keccak.Split.ColumnParity

set_option maxRecDepth 16384

/- The no-cache column-parity worker (CSR 0x7CD): its equations, the timestamp
   alignment query and all 22 fixed-table queries over the supplied setup, plus its
   delegation clock and memory-port metadata. Each port has its own borrowed
   timestamp comparison, as in the other delegation workers. -/
import_clean importedConstraints from "../../cs/compiled_circuits/keccak_column_parity_layout_no_caches_gkr.json" keccak_column_parity_lookups delegation_metadata

/-- The operation core plus the invocation and timestamp-comparison queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ColumnParity
