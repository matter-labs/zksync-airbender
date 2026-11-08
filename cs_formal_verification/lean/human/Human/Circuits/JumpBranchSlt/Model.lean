import Human.Circuits.JumpBranchSlt.Artifact
import Human.Helpers.Properties
import Human.Helpers.Decoder.PooledProgram
import Human.Helpers.Context.RowContext
import Human.Helpers.Tables.Subword

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
