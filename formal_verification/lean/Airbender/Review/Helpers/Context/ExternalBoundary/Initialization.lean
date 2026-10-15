import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.ExternalBoundary.Initialization
open Trace

/-- Address geometry is supplied by the statement/layout, rather than a fixed
    verifier ceiling. Two low byte bits give four bytes per initialized word. -/
structure Geometry where
  words : Nat
  slots : Nat
  positive : 0 < words
  extent : slots * (4 * words) ≤ 2 ^ 32

/-- Explicit logical interface for AIH-334 window validation. The EVM source
    check is implemented and tested; its formal correspondence to this record
    remains external. External statement validation selects distinct windows.
    Strict ordering or a checked production constant may establish this field; sparse windows and
    reversed distinct windows have the same memory-uniqueness meaning. -/
structure Selection (geometry : Geometry) where
  indices : List (Fin geometry.slots)
  unique : indices.Nodup

abbrev Position (geometry : Geometry) := Fin geometry.slots × Fin geometry.words

def address (position : Position geometry) : Nat :=
  4 * (position.1.val * geometry.words + position.2.val)

def cell (position : Position geometry) : Cell :=
  .ram (BitVec.ofNat 32 (address position))

def registers : List Cell :=
  (List.finRange 32).map fun index => .register (BitVec.ofNat 5 index.val)

/-- Native register and selected RAM domains, without truncating a top index or
    adding contiguity/full-coverage requirements. -/
def cells (selection : Selection geometry) : List Cell :=
  registers ++ (selection.indices.product (List.finRange geometry.words)).map cell

end Airbender.ExternalBoundary.Initialization
