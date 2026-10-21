import Airbender.Review.Circuits.SubwordMemory.AddressModel

namespace Airbender.SubwordMemory
open Arithmetic Verification
set_option autoImplicit false

def Operation.byte : Operation → Bool
  | .lb | .lbu | .sb => true | _ => false

def Operation.unsigned : Operation → Bool
  | .lbu | .lhu => true | _ => false

def Operation.width (operation : Operation) : Nat := if operation.byte then 1 else 2

/-- Actual mixed-port data and written data. -/
def dataWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 32).val,(w 33).val⟩
def writtenWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 39).val,(w 40).val⟩

/-- Native ROM uses one aligned word table. Architectural Sail memory binding
    remains separate; RAM data is the actual mixed-port read. -/
def loadWord (rom : WordROM) (w : Nat → ZMod mersenne31Modulus) : Word :=
  if (w 20).val < 64 then Word.ofBitVec (rom.word ((cellWord w).value / 4)) else dataWord w

/-- Byte/halfword load result functions use the original Sail extension and actual
    native words. This states data effects, not original instruction execution. -/
structure NativeLoadEffects (rom : WordROM) (w : Nat → ZMod mersenne31Modulus)
    (entry : ProgramEntry) : Prop where
  size : w 24 = 1
  offsetBound : (w 22).val < 4
  upper : (w 25).val = (w 22).val / 2
  alignment : entry.data.family.byte = false →
    (entry.data.family.mask = 1 ∨ entry.data.rd ≠ 0) → (w 22).val % 2 = 0
  load : entry.data.family.mask = 0 →
    (writtenWord w).toBitVec = if entry.data.rd = 0 then 0 else
      SailRV32.Functions.extend_value entry.data.family.unsigned
        (((loadWord rom w).toBitVec >>> (8 * (w 22).val)).setWidth (8 * entry.data.family.width))

end Airbender.SubwordMemory
