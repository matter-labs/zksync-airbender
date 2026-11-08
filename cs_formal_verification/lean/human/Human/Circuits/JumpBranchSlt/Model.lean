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

/-- Standard Sail clauses covered by this comparison slice. -/
inductive Opcode where
  | slt | slti | sltu | sltiu
  deriving Repr, DecidableEq

end Airbender.JumpBranchSlt.Comparison
