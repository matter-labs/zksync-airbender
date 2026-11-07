import Airbender.Review.Helpers.Memory.InitialImage
import Airbender.Review.Circuits.ReducedMachine.WordMemoryDecoder

namespace Airbender.ReducedMachine.Native
open Trace Arithmetic
set_option autoImplicit false

/-- Actual mixed-port cells. A load shadow is a native logical memory event;
    this address reference does not identify its value with architectural ROM. -/
def wordMemoryPortCells (w : Nat → ZMod mersenne31Modulus) (entry : WordMemoryProgramEntry) : Vector Cell 3 :=
  #v[.register entry.data.rs1,
    if entry.data.family then .register entry.data.rs2 else .ram (wordMemoryAddressWord w).toBitVec,
    if entry.data.family then .ram (wordMemoryAddressWord w).toBitVec else .register entry.data.rd]

end Airbender.ReducedMachine.Native
