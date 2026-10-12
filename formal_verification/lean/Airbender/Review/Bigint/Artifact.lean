import Airbender.Import.Embed
import Mathlib.Tactic.FinCases

namespace Airbender.Bigint

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- All native equations, ranges and fixed queries. Setup rows remain an interface.
import_clean importedConstraints from "../../cs/compiled_circuits/bigint_with_extended_control_layout_no_caches_gkr.json" bigint_lookups delegation_metadata

/-- Native invocation ranges and every timestamp comparison, in addition to
    the family's retained equations and modeled table queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev controlBits := #v[59, 60, 61, 62, 63, 64, 65, 66]
-- Same order as common_constants/src/delegation_types/bigint_with_control.rs;
-- carry is bit six and is excluded from opcode exclusivity.
abbrev operations := #v[59, 60, 61, 62, 63, 64, 66]
def leftLimbs : Vector Nat 16 := Vector.ofFn fun i => 5 + 4 * (i.val / 2) + i.val % 2
def rightLimbs : Vector Nat 16 := Vector.ofFn fun i => 39 + i.val
def writtenLimbs : Vector Nat 16 := Vector.ofFn fun i => 7 + 4 * (i.val / 2) + i.val % 2
end Variables

end Airbender.Bigint
