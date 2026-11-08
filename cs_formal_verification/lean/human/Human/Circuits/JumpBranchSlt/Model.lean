module
public import Human.Circuits.JumpBranchSlt.Artifact
public import Human.Helpers.Properties
public import Human.Helpers.Decoder.PooledProgram
public import Human.Helpers.Context.RowContext
public import Human.Helpers.Tables.Subword

@[expose] public section

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

end Airbender.JumpBranchSlt

namespace Airbender.JumpBranchSlt.Comparison
open Airbender.Arithmetic
open Variables
open Trace

/-- The comparison opcodes covered by this slice (SLT, SLTI, SLTU, SLTIU). -/
inductive Opcode where
  | slt | slti | sltu | sltiu
  deriving Repr, DecidableEq

end Airbender.JumpBranchSlt.Comparison
