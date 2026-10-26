import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.Compiler.ROMNative.WordFullPublic

/-- Every word in the retained ROM domain is present in the public cells. -/
def CoversROM (cells : List Trace.Cell) : Prop :=
  ∀ index : Fin 1048576, Trace.Cell.ram (BitVec.ofNat 32 (4 * index.val)) ∈ cells

end Airbender.Compiler.ROMNative.WordFullPublic
