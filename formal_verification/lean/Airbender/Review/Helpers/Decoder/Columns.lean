import Airbender.Review.Helpers.Context.Columns

namespace Airbender.Trace

/-- Logical variable IDs of v2's ten-column preprocessed decoder query.
    Native metadata supplies placement, including the separate zero flag and
    already-packed mask. Table contents and Sail decoding remain separate. -/
structure DecoderColumns where
  rs1 : Nat
  rs2 : Nat
  rd : Nat
  rdIsZero : Nat
  immediate : Vector Nat 2
  funct3 : Nat
  mask : Nat
  deriving DecidableEq

end Airbender.Trace
