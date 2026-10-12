import Airbender.Import.Embed

namespace Airbender.AddSub

-- The JSON's retained equations and range queries, emitted as native Clean operations.
import_clean importedConstraints from "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json" trace_metadata

/-- Arithmetic, word ranges and the eight native timestamp queries. Decoder and
    global state/memory matching are separate trace obligations. -/
def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

end Airbender.AddSub
