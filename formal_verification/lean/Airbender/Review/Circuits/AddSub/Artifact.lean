import Airbender.Import.Embed
import Airbender.Review.Helpers.Core.Word

namespace Airbender.AddSub
open Arithmetic

-- The JSON's retained equations and range queries, emitted as native Clean operations.
import_clean importedConstraints from "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json" trace_metadata

/-- Arithmetic, word ranges and the eight native timestamp queries. Decoder and
    global state/memory matching are separate trace obligations. -/
def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

/-- PC limbs in the imported artifact. Initial bounds come from the state interface;
    final bounds are enforced by the imported lookups. -/
structure PCMapping {p : Nat} (initial final : Word) (w : Nat → ZMod p) : Prop where
  initialLo : w 0 = (initial.lo : ZMod p)
  initialHi : w 1 = (initial.hi : ZMod p)
  finalLo : final.lo = (w 19).val
  finalHi : final.hi = (w 20).val

end Airbender.AddSub
