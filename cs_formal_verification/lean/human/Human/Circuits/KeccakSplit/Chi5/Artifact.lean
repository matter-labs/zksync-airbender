module
public import Human.Import.Embed

@[expose] public section

namespace Airbender.Keccak.Split.Chi5

set_option maxRecDepth 16384

/- The no-cache chi worker (CSR 0x7CE): its equations (including the grouped
   timestamp equations), the alignment query and all 17 fixed-table queries over the
   supplied setup, plus its grouped clock and memory-port metadata. -/
import_clean importedConstraints from "../../cs/compiled_circuits/keccak_chi5_layout_no_caches_gkr.json" keccak_chi5_lookups split_delegation_timestamps

/-- The operation core plus the invocation timestamp query. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 11)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.Chi5
