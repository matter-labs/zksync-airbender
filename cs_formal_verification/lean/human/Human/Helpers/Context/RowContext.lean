import Human.Helpers.Memory.InitialImage

namespace Airbender.Trace
open Arithmetic

/-- This row's writes in reverse port order. `WriteHistory` applies the tail
    first, so their Sail effects occur in the original native port order. -/
def rowWriteValues {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : List (Nat × Nat) :=
  row.writes.reverse.map fun token => (token.address, token.value)

end Airbender.Trace
