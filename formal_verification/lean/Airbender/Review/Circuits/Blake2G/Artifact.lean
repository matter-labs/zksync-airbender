import Airbender.Import.Embed

namespace Airbender.Blake2G

-- The supplied tagged setup is an explicit interface, not a witness-generation hint.
import_clean importedConstraints from "../../cs/compiled_circuits/blake2_g_function_layout_no_caches_gkr.json" blake_g_lookups delegation_metadata

/-- Native invocation ranges and every timestamp comparison, in addition to
    the family's retained equations and modeled table queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev execute := 0
abbrev controlReadLo := 3
abbrev controlReadHi := 4
abbrev controlWriteLo := 5
abbrev controlWriteHi := 6
abbrev stateOffsetColumns := #v[7, 8, 9, 10]
abbrev messageOffsetColumns := #v[11, 12]
abbrev statePointerLo := 13
abbrev messagePointerLo := 31
abbrev booleanColumns := #v[0, 37, 38, 39, 40, 49, 50, 65, 66, 67, 68, 75, 76,
  85, 88, 91, 94, 97, 100, 103, 106, 109]
end Variables

end Airbender.Blake2G
