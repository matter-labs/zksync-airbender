import Airbender.Review.Circuits.MulDiv.Artifact
import Airbender.Review.Helpers.Core.Word

namespace Airbender.MulDiv
open Arithmetic

inductive Operation where
  | mul | mulhu | divu | remu

def Operation.selector : Operation → Fin 4
  | .mul => 0 | .mulhu => 1 | .divu => 2 | .remu => 3

/-- Actual unsigned v2 packed mask, independent of the destination zero flag. -/
def Operation.nativeMask : Operation → Nat
  | .mul => 2 | .mulhu => 0 | .divu => 3 | .remu => 1

def Operation.division : Operation → Bool
  | .divu | .remu => true | _ => false

def Operation.lowHalf : Operation → Bool
  | .mul | .divu => true | _ => false

/-- Unsigned RV32 numerical reference; the original Sail connection is separate. -/
def Operation.result (operation : Operation) (left right : Word) : Nat :=
  match operation with
  | .mul => left.value * right.value % wordModulus
  | .mulhu => left.value * right.value / wordModulus
  | .divu => if right.value = 0 then wordModulus - 1 else left.value / right.value
  | .remu => left.value % right.value

def left (w : Nat → ZMod p) : Word := ⟨(w 19).val, (w 20).val⟩
def right (w : Nat → ZMod p) : Word := ⟨(w 21).val, (w 22).val⟩
def selectedWord (w : Nat → ZMod p) : Word := ⟨(w 50).val, (w 51).val⟩
def writtenWord (w : Nat → ZMod p) : Word := ⟨(w 60).val, (w 61).val⟩

end Airbender.MulDiv
