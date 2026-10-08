import Airbender.Import.Embed
import Mathlib.Tactic.FinCases

namespace Airbender.Bigint

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- All native equations, ranges and fixed queries. Setup rows remain an interface.
import_clean importedConstraints from "../../cs/compiled_circuits/bigint_with_extended_control_layout_no_caches_gkr.json" bigint_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 136 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 95 := rfl

namespace Variables
abbrev controlBits := #v[59, 60, 61, 62, 63, 64, 65, 66]
-- Same order as common_constants/src/delegation_types/bigint_with_control.rs;
-- carry is bit six and is excluded from opcode exclusivity.
abbrev operations := #v[59, 60, 61, 62, 63, 64, 66]
end Variables

theorem control_roles :
    importedConstraintsVariableNames.lookup 55 = some "control read/write from x12 read[0]" ∧
    importedConstraintsVariableNames.lookup 56 = some "control read/write from x12 read[1]" ∧
    importedConstraintsVariableNames.lookup 57 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 58 = some "control read/write from x12 write[0]" := by decide

end Airbender.Bigint
