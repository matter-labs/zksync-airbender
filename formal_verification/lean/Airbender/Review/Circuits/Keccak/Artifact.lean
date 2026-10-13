import Airbender.Import.Embed

namespace Airbender.Keccak

set_option maxRecDepth 16384

-- All fixed queries use the supplied tagged setup. Its rows remain an explicit
-- interface; this import does not reconstruct or assume the Keccak operations.
import_clean importedConstraints from "../../cs/compiled_circuits/keccak_special5_layout_no_caches_gkr.json" keccak_lookups delegation_metadata

/-- Native invocation ranges and every timestamp comparison, in addition to
    the family's retained equations and modeled table queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 42 := rfl

namespace Variables
abbrev execute := 0
abbrev controlReadLo := 3
abbrev controlReadHi := 4
abbrev controlWriteLo := 5
abbrev controlWriteHi := 6
abbrev statePointerLo := 13
abbrev statePointerHi := 14
abbrev modeColumns := #v[63, 64, 65, 66, 67, 68, 69]
abbrev iterationColumns := #v[70, 71, 72, 73, 74]
abbrev roundColumns := #v[75, 76, 77, 78, 79]
end Variables

end Airbender.Keccak
