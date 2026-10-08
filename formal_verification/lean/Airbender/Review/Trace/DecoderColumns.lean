import Airbender.Review.Trace.Columns

namespace Airbender.Trace

/-- Logical variables of Rust's native DecoderPlacementDescription, resolved
    through the JSON placement map. Table contents and Sail decoding are separate. -/
structure DecoderColumns where
  rs1 : Nat
  rs2 : Nat
  rd : Nat
  immediate : Vector Nat 2
  funct3 : Option Nat
  flags : Array Nat
  deriving DecidableEq

end Airbender.Trace
