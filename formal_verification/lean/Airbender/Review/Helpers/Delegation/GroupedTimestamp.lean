import Mathlib.Data.Vector.Basic

namespace Airbender.Delegation

/-- Native split-worker metadata for one shared read timestamp. `members`
indexes the worker's memory ports. The grouped comparison equations are in
the imported circuit; this descriptor alone asserts no timing inequality. -/
structure GroupedTimestamp where
  previous : Vector Nat 2
  borrow : Nat
  members : Array Nat

end Airbender.Delegation
