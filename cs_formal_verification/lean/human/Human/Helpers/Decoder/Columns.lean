import Human.Helpers.Context.Columns

namespace Airbender.Trace

/-- Logical variables of Rust's native DecoderPlacementDescription, resolved
    through the JSON placement map. Table contents and Sail decoding are separate. -/
structure DecoderColumns where
  rs1 : Nat
  rs2 : Nat
  rd : Nat
  /-- Variable IDs for the preprocessed native immediate limbs. -/
  immediate : Vector Nat 2
  /-- Optional operation-tag variable; absent tags contribute zero to the query. -/
  funct3 : Option Nat
  /-- Selector variable IDs in bit order; `nativeDecoderQuery` packs them into the mask. -/
  flags : Array Nat
  deriving DecidableEq

end Airbender.Trace
