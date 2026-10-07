import Airbender.Import.Embed

namespace Airbender.Blake2Round

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Native Clean equations and queries; setup provenance and memory transport remain external.
import_clean importedConstraints from "../../cs/compiled_circuits/blake2_with_extended_control_layout_no_caches_gkr.json" blake_round_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 352 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 210 := rfl

namespace Variables
abbrev execute := 0
abbrev controlReadLo := 135
abbrev controlReadHi := 136
abbrev controlWriteLo := 137
abbrev controlWriteHi := 138
abbrev controlBits := #v[139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
end Variables

theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 135 = some "control read/write from x12 read[0]" ∧
    importedConstraintsVariableNames.lookup 136 = some "control read/write from x12 read[1]" ∧
    importedConstraintsVariableNames.lookup 137 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 138 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 152 = some "perform final xor flag" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.Blake2Round
