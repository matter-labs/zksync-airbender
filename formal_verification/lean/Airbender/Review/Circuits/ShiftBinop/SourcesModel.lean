import Airbender.Review.Circuits.ShiftBinop.ShiftModel

namespace Airbender.ShiftBinop
set_option autoImplicit false

/-- Canonical interpretation of actual native packed shift keys, after deriving
    source-read bounds from initialized matching. These are observed columns;
    original Sail register/cell and whole-shift execution remain separate. -/
structure ShiftSourceBinding (w : Nat → ZMod mersenne31Modulus) (kind : ShiftKind) : Prop where
  sourceBound : (left w).Bounded
  selectedBound : (selectedWord w).Bounded
  amount : (w 29).val = (w 27).val % 32
  packedKey : ∀ slot : Fin 3, (w (43 + 4 * slot.val)).val =
    if kind.parts[slot.val] = .zero then 0
    else (w (kind.sourceColumn slot)).val + 65536 * (w 29).val
  sourceLimb : ∀ slot : Fin 3, kind.parts[slot.val] ≠ .zero →
    (w (43 + 4 * slot.val)).val % 65536 = (w (kind.sourceColumn slot)).val
  shiftAmount : ∀ slot : Fin 3, kind.parts[slot.val] ≠ .zero →
    (w (43 + 4 * slot.val)).val / 65536 = (w 29).val

end Airbender.ShiftBinop
