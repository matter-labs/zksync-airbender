import Mathlib.Data.Vector.Basic

namespace Airbender.Delegation

/-- Native split-worker metadata for one shared read timestamp. `members`
indexes the worker's memory ports. The grouped comparison equations are in
the imported circuit; this descriptor alone asserts no timing inequality. -/
structure GroupedTimestamp where
  previous : Vector Nat 2
  borrow : Nat
  members : Array Nat
  /-- Subtract this column from `borrow` when the native borrow is derived. -/
  subtrahend : Option Nat := none

/-- Evaluate the native borrow. Grouped comparisons derive it from the high
invocation limb and the high previous-time limb. -/
def GroupedTimestamp.borrowValue {F : Type} [Sub F]
    (group : GroupedTimestamp) (w : Nat → F) : F :=
  match group.subtrahend with
  | none => w group.borrow
  | some column => w group.borrow - w column

end Airbender.Delegation
