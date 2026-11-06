import Airbender.Review.Circuits.ReducedMachine.Arithmetic
import Airbender.Review.Circuits.ReducedMachine.ShiftResult
import Airbender.Review.Circuits.ReducedMachine.PC

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- Actual native decoded immediate; original public decoding is a separate connection. -/
def arithmeticImmediateWord (w : Nat → ZMod mersenne31Modulus) : Word :=
  ⟨(w 9).val,(w 10).val⟩

/-- RV32 numerical references at native source/selected-operand/PC/immediate words.
    Original retained Sail clauses and initialized state transport are separate. -/
def ArithmeticMode.result (mode : ArithmeticMode) (source operand pc immediate : BitVec 32) : BitVec 32 :=
  match mode with
  | .add | .addi => source + operand
  | .sub => source - operand
  | .lui => immediate
  | .auipc => pc + immediate

end Airbender.ReducedMachine.Native
