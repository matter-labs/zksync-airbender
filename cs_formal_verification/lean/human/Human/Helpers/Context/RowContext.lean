module
public import Human.Helpers.Memory.InitialImage

@[expose] public section

namespace Airbender.Trace
open Arithmetic

/-- This row's writes in reverse port order. `RVWriteHistory` applies the tail
    first, so their effects occur in the original native port order. -/
def rowWriteValues {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : List (Nat × Nat) :=
  row.writes.reverse.map fun token => (token.address, token.value)

end Airbender.Trace
