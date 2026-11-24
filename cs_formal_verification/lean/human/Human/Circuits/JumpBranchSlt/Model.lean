module

@[expose] public section

namespace Airbender.JumpBranchSlt.Comparison

/-- The comparison opcodes covered by this slice (SLT, SLTI, SLTU, SLTIU). -/
inductive Opcode where
  | slt | slti | sltu | sltiu
  deriving Repr, DecidableEq

end Airbender.JumpBranchSlt.Comparison
