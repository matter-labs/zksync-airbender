import Human.Circuits.JumpBranchSlt.Model
import Human.Helpers.Properties

namespace Airbender.JumpBranchSlt.Jump
open Airbender.Arithmetic
open Variables
open Trace

inductive Instruction where
  | jal (offset : BitVec 21)
  | jalr (offset : BitVec 12)

def Instruction.indirect : Instruction → Bool
  | .jal _ => false | .jalr _ => true

end Airbender.JumpBranchSlt.Jump
