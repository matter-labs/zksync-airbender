import Airbender.Import.Embed

namespace Airbender.SubwordMemory

-- All retained equations, five ranges and both non-decoder lookup sets.
-- The tagged setup table is caller-supplied; its fixed/ROM semantics and
-- program/setup binding are separate obligations. RAM load/store claims are in Theorems.
import_clean importedConstraints from "../../cs/compiled_circuits/mem_subword_only_layout_no_caches_gkr.json" subword_memory_lookups trace_metadata

def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev initialPCLo := 0
abbrev initialPCHi := 1
abbrev execute := 4
abbrev storeSelector := 10
abbrev byteSelector := 11
abbrev signedSelector := 12
abbrev finalPCLo := 13
abbrev finalPCHi := 14
end Variables

end Airbender.SubwordMemory
