module
public import Human.Circuits.JumpBranchSlt.Model
public import Human.Helpers.Properties

@[expose] public section

namespace Airbender.JumpBranchSlt.Jump

inductive Instruction where
  | jal (offset : BitVec 21)
  | jalr (offset : BitVec 12)

def Instruction.indirect : Instruction → Bool
  | .jal _ => false | .jalr _ => true

end Airbender.JumpBranchSlt.Jump
