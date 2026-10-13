import Airbender.Review.Helpers.Word
import Mathlib.Data.ZMod.Basic

namespace Airbender.Verification

/-- Logical-variable projection of JSON `IndirectRam` metadata. This describes
    a port, not its memory-argument enforcement. Columns name the same witness
    variables as the imported Clean constraints. -/
structure IndirectPort where
  register : Nat
  access : Nat
  baseColumns : Vector Nat 2
  scale : Nat
  offsetColumn : Option Nat
  constant : Nat
  readColumns : Vector Nat 2
  writeColumns : Option (Vector Nat 2)
  deriving Repr, DecidableEq

/-- The field-limb address emitted for an indirect port. Keep the limbs intact
    until initialized memory matching proves they form a valid public address. -/
def IndirectPort.rawAddress {p : Nat} (port : IndirectPort) (w : Nat → ZMod p) :
    ZMod p × ZMod p :=
  (w port.baseColumns[0] + (port.scale : ZMod p) * port.offsetColumn.elim 0 w + port.constant,
    w port.baseColumns[1])

/-- Rust's `U32SpaceSpecialIndirect`: offset is added to the low limb; the
    high limb is unchanged. Correct word arithmetic requires excluding carry. -/
def IndirectPort.address {p : Nat} (port : IndirectPort) (w : Nat → ZMod p) : BitVec 32 :=
  let offset := port.offsetColumn.elim 0 w
  (Arithmetic.Word.mk
    (w port.baseColumns[0] + (port.scale : ZMod p) * offset + port.constant).val
    (w port.baseColumns[1]).val).toBitVec

end Airbender.Verification
