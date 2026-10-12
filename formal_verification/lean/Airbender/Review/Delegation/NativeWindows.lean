import Airbender.Review.Delegation.Memory

namespace Airbender.Delegation
open Trace

/-- All imported worker ports write at invocation plus two, in native clock units. -/
def Row.writeTime (row : Row p) : Nat :=
  (timeOfPair ((rawPair row.assignment row.columns.invocation).1 + 2,
    (rawPair row.assignment row.columns.invocation).2)).value

/-- Complete native rows whose writes lie between the two cuts. -/
def MemoryData.windowRows (data : MemoryData p) (lower upper : Nat) : List (Row p) :=
  data.rows.filter fun row => decide (lower < row.writeTime ∧ row.writeTime ≤ upper)

/-- Complete native rows written at or before the first cut. -/
def MemoryData.prefixRows (data : MemoryData p) (cutoff : Nat) : List (Row p) :=
  data.rows.filter fun row => decide (row.writeTime ≤ cutoff)

end Airbender.Delegation
