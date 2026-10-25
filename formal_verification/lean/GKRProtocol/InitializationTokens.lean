import GKRProtocol.MemoryTokens
import Airbender.Review.Circuits.Initialization.Model

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

/-- Raw source initialization/teardown tuple, before public address bounds.
The second set adds the actual imported high-limb stride in the base field. -/
def sourceBoundaryToken (memory : Source.MemoryValues) (stageKind : Initialization.Phase)
    (set stride : Nat) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 1 (Nat.pair (memory.initializationAddress 0).val
      (memory.initializationAddress 1 + (set * stride : Nat)).val),
    match stageKind with
    | .initial => (0, 0)
    | .terminal => (memory.teardownTimestamp set 0, memory.teardownTimestamp set 1),
    match stageKind with
    | .initial => 0
    | .terminal => Nat.pair (memory.teardownValue set 0).val (memory.teardownValue set 1).val⟩

theorem source_boundary_leaf (layout : Initialization.Layout)
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (memory : Source.MemoryValues) (raw : Initialization.Raw babyBearModulus)
    (stageKind : Initialization.Phase) (set : Fin layout.columns.size) (row : Fin layout.rows)
    (low : memory.initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : memory.initializationAddress 1 + (set.val * layout.stride : Nat) =
      (Initialization.addressHi layout parameters set.val row.val : Source.BaseField))
    (lowBound : Initialization.addressLo row.val < babyBearModulus)
    (highBound : Initialization.addressHi layout parameters set.val row.val < babyBearModulus)
    (timeLo : memory.teardownTimestamp set.val 0 = raw row.val layout.columns[set].timeLo)
    (timeHi : memory.teardownTimestamp set.val 1 = raw row.val layout.columns[set].timeHi)
    (valueLo : memory.teardownValue set.val 0 = raw row.val layout.columns[set].valueLo)
    (valueHi : memory.teardownValue set.val 1 = raw row.val layout.columns[set].valueHi) :
    sourceBoundaryToken memory stageKind set.val layout.stride =
      (Initialization.Leaf.mk stageKind set.val layout.columns[set]).token layout parameters raw row.val := by
  cases stageKind <;>
    simp only [sourceBoundaryToken, Initialization.Leaf.token, Initialization.Leaf.time,
      Initialization.Leaf.value, low, high, timeLo, timeHi, valueLo, valueHi,
      ZMod.val_natCast, Nat.mod_eq_of_lt lowBound, Nat.mod_eq_of_lt highBound]
  all_goals rfl

end Airbender.Compiler
