import Airbender.Review.Circuits.ReducedMachine.Decoder

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- Original RV32 numerical references. Architectural state transport is separate. -/
def ShiftMode.result (mode : ShiftMode) (source : BitVec 32) (amount : Nat) : BitVec 32 :=
  match mode with
  | .left => source <<< amount
  | .right => source >>> amount
  | .arithmetic => source.sshiftRight amount

def sourceWord (w : Nat → ZMod mersenne31Modulus) : Word :=
  ⟨(source1 w)[0].val,(source1 w)[1].val⟩

def operandWord (w : Nat → ZMod mersenne31Modulus) : Word :=
  ⟨(source2 w)[0].val,(source2 w)[1].val⟩

def candidateWord (w : Nat → ZMod mersenne31Modulus) : Word :=
  ⟨(w 116).val,(w 117).val⟩

def writtenWord (w : Nat → ZMod mersenne31Modulus) : Word :=
  ⟨(rdWrite w)[0].val,(rdWrite w)[1].val⟩

end Airbender.ReducedMachine.Native
