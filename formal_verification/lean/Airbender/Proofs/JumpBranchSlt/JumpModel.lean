import Airbender.Proofs.Arithmetic.Word
import Airbender.Review.Helpers.Core.Sail

namespace Airbender.JumpBranchSlt.Jump
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail

inductive Instruction where
  | jal (offset : BitVec 21)
  | jalr (offset : BitVec 12)

def Instruction.indirect : Instruction → Bool
  | .jal _ => false | .jalr _ => true

/-- Native encodings and independently fixed architectural inputs. -/
structure Input where
  instruction : Instruction
  source : Word
  offset : Word
  pc : Word
  rs1 : SailRV32.regidx
  rd : SailRV32.regidx
  before : Sail.State

def Input.base (input : Input) : Word :=
  if input.instruction.indirect then input.source else input.pc

/-- Original Sail constructor used by both public-program binding and execution. -/
def instruction (input : Input) : SailRV32.instruction :=
  match input.instruction with
  | .jal imm => .JAL (imm, input.rd)
  | .jalr imm => .JALR (imm, input.rs1, input.rd)

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  (Sail.registerClause (instruction input)).get (by cases h_instruction : input.instruction <;> simp_all [instruction, Sail.registerClause])

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

end Airbender.JumpBranchSlt.Jump
