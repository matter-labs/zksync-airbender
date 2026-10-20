import Human.Import.Embed

namespace Airbender.MulDiv

-- Retained equations, fixed queries and native trace/decoder metadata.
-- Logical matching and modeled fixed-table provenance remain external.
import_clean importedConstraints from "../../cs/compiled_circuits/unsigned_mul_div_layout_no_caches_gkr.json" mul_div_lookups trace_metadata

def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

end Airbender.MulDiv
