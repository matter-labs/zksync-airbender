import Airbender.Review.Helpers.Core.Sail

namespace Airbender.Reference.RiscV
open Airbender.Arithmetic

/-- Tags selecting the upstream execution clauses covered by this pilot. -/
inductive Opcode where
  | add | addi | sub | lui | auipc
  deriving Repr, DecidableEq

/-- Original instruction tag and preprocessed words supplied to the arithmetic circuit. -/
structure RowInput where
  opcode : Opcode
  left : Word
  right : Word
  immediate : Word
  pc : Word

end Airbender.Reference.RiscV

namespace Airbender.Reference.RiscV.Sail
open Airbender.Arithmetic

/-- An original decoded instruction and the preprocessed words exposed to the circuit.
    The Sail state is external input, not a circuit-generated witness. -/
structure Input where
  /-- Circuit operands after decoder preprocessing. -/
  row : RowInput
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  /-- Original 12-bit encoding; for ADDI, `row.immediate` is its 32-bit sign extension. -/
  encodedImmediate : BitVec 12
  /-- Original U-type encoding; Sail appends twelve zero bits. -/
  encodedUpperImmediate : BitVec 20
  before : State

/-- Original Sail instruction selected by the ADD/SUB input. The same value
    binds the public decoder entry and selects the generated execution clause. -/
def instruction (input : Input) : SailRV32.instruction :=
  match input.row.opcode with
  | .add => .RTYPE (input.rs2, input.rs1, input.rd, .ADD)
  | .addi => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .ADDI)
  | .sub => .RTYPE (input.rs2, input.rs1, input.rd, .SUB)
  | .lui => .UTYPE (input.encodedUpperImmediate, input.rd, .LUI)
  | .auipc => .UTYPE (input.encodedUpperImmediate, input.rd, .AUIPC)

/-- Select the actual generated Sail clause for this supported instruction. -/
def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  (registerClause (instruction input)).get (by cases h_opcode : input.row.opcode <;> simp_all [instruction, registerClause])

/-- Standard instructions use the actual generated Sail execution clauses. -/
abbrev spec (input : Input) (output : Output) : Prop :=
  stepSpec input.before (execution input) input.rd output

end Airbender.Reference.RiscV.Sail
