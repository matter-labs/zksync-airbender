import Airbender.Review.Circuits.ShiftBinop.RoutingModel
import Airbender.Review.Helpers.Tables.Binary

namespace Airbender.ShiftBinop
open Arithmetic Verification
set_option autoImplicit false

def binaryOperation : BinaryKind → Operation
  | .xor => .xor | .or => .or | .and => .and

def left (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 23).val, (w 24).val⟩
def right (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 27).val, (w 28).val⟩
def selectedWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 55).val, (w 56).val⟩
def writtenWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 59).val, (w 60).val⟩

/-- Numerical native row result. Architectural register/history transport is separate. -/
structure BinaryResult (w : Nat → ZMod mersenne31Modulus) (kind : BinaryKind)
    (discarded : Bool) : Prop where
  leftBound : (left w).Bounded
  rightBound : (right w).Bounded
  selectedBound : (selectedWord w).Bounded
  selected : (selectedWord w).toBitVec = byteOperation kind.tag (left w).toBitVec (right w).toBitVec
  written : writtenWord w = if discarded then ⟨0,0⟩ else selectedWord w

end Airbender.ShiftBinop
