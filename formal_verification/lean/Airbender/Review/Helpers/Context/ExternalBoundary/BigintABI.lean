import Airbender.Review.Circuits.Bigint.Execution

namespace Airbender.ExternalBoundary.BigintABI
open Arithmetic

/-- Successful bigint calls use exactly one opcode and an independent carry
    bit. The carry position is six; COPY occupies bit seven. -/
structure Command where
  opcode : Fin 7
  carry : Bool
  deriving DecidableEq

def Command.bit (command : Command) : Fin 8 :=
  (#v[0, 1, 2, 3, 4, 5, 7] : Vector (Fin 8) 7)[command.opcode]

def Command.bits (command : Command) : Vector Bool 8 :=
  Vector.ofFn fun i => decide (i = command.bit) || (decide (i = 6) && command.carry)

def Command.word (command : Command) : Word := ⟨Bigint.Control.mask command.bits, 0⟩

/-- Actual pre-write x12 observation at the imported nineteenth port. -/
def input (w : Nat → ZMod p) : Word :=
  (Trace.readToken w Bigint.importedConstraintsMemoryPorts[18]).word

/-- Lower-level successful-call control binding for F02, not a native
    validation check or a proof of the complete custom-CSR ABI.
    External successful-call ABI binding to the full native x12 read, including
    its high limb. This is an additional call-reference/acceptance obligation;
    existing native acceptance alone admits controls zero and 65537. -/
def Binding (w : Nat → ZMod p) (command : Command) : Prop := input w = command.word

end Airbender.ExternalBoundary.BigintABI
