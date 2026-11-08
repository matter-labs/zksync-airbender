import Airbender.Review.Circuits.ReducedMachine.Scalar16Lookups

namespace Airbender.NativeInitializationSorted
open Airbender.NativeInitializationOrdering

/-- Canonical unsigned radix address of the ACTUAL initialization record.
    Bounds are derived from the full-family logical lookup boundary. -/
def addressValue (w : Nat → F) : Nat := (address w)[0].val+65536*(address w)[1].val

end Airbender.NativeInitializationSorted
