import Airbender.Review.Circuits.ReducedMachine.ShiftResult

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- Original Sail instruction form; the selected decoder projection restricts
    supported operations separately. This does not inspect a supplied selector. -/
def shiftUsesRegister : SailRV32.instruction → Bool
  | .RTYPE _ => true
  | _ => false

/-- Actual readonly second-port word, including immediate/x0 participation. -/
def registerOperandWord (w : Nat → ZMod mersenne31Modulus) : Word :=
  let value := importedConstraintsMemoryPorts[1].readValue.evaluate w
  ⟨value[0].val,value[1].val⟩

end Airbender.ReducedMachine.Native
