import Airbender.Review.Circuits.Keccak.Artifact
import Airbender.Review.Helpers.Properties

namespace Airbender.Keccak
open scoped BigOperators

/-- Local structural guarantees, independent of the supplied fixed-table rows.
    Active rows select exactly one of seven operations and one of five iterations;
    inactive rows select none. Round bits alone do not enforce the 24-round schedule.
    Lane operations, the full permutation, and memory transport are separate claims. -/
structure LocalChecks {p : Nat} (w : Nat → ZMod p) : Prop where
  execute : w Variables.execute = 0 ∨ w Variables.execute = 1
  controlBits : ∀ i : Fin 17, w (63 + i.val) = 0 ∨ w (63 + i.val) = 1
  readHigh : w Variables.controlReadHi = 0
  writeHigh : w Variables.controlWriteHi = 0
  readBound : (w Variables.controlReadLo).val < 2048
  modeCount : (∑ i : Fin 7, (w Variables.modeColumns[i]).val) = (w Variables.execute).val
  iterationCount : (∑ i : Fin 5, (w Variables.iterationColumns[i]).val) = (w Variables.execute).val
  pointerAlignment : (w Variables.statePointerLo).val % 256 = 0

end Airbender.Keccak
