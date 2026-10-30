import Lean

namespace Airbender.Setup.SourceIndices

/-- Decode each stored index in source order. Keep recursion in tail position. -/
def go (base : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, earlier => earlier.reverse
  | remaining + 1, value, earlier =>
    go base remaining (value / base) ((value % base) :: earlier)

def decode (base count packed : Nat) : List Nat := go base count packed []

end Airbender.Setup.SourceIndices
