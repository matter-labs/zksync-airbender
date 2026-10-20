import Human.Import.Embed
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Round

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Native Clean equations and queries; setup provenance and memory transport remain external.
import_clean importedConstraints from "../../cs/compiled_circuits/blake2_with_extended_control_layout_no_caches_gkr.json" blake_round_lookups delegation_metadata

/-- Native invocation ranges and every timestamp comparison, in addition to
    the family's retained equations and modeled table queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev execute := 0
abbrev controlReadLo := 135
abbrev controlReadHi := 136
abbrev controlWriteLo := 137
abbrev controlWriteHi := 138
abbrev controlBits := #v[139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
def stateReads : Vector (Nat × Nat) 8 := Vector.ofFn fun i => (5 + 4 * i.val, 6 + 4 * i.val)
def extendedReads : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (37 + 4 * i.val, 38 + 4 * i.val)
def messageReads : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (103 + 2 * i.val, 104 + 2 * i.val)
def chainingInputs : Vector (Nat × Nat) 8 :=
  #v[(154, 156), (158, 160), (162, 164), (166, 168),
    (170, 172), (174, 176), (178, 180), (182, 184)]
def preparedState : Vector (Nat × Nat) 16 :=
  #v[(155, 157), (159, 161), (163, 165), (167, 169),
    (171, 173), (175, 177), (179, 181), (183, 185),
    (186, 187), (188, 189), (190, 191), (192, 193),
    (198, 199), (194, 195), (200, 201), (196, 197)]
def preparedMessage : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (204 + 2 * i.val, 205 + 2 * i.val)
abbrev roundBits := #v[142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
def scheduledMessage : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (236 + 2 * i.val, 237 + 2 * i.val)
end Variables

end Airbender.Blake2Round
