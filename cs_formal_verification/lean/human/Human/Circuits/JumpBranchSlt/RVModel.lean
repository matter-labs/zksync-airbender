module
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.Helpers.Core.CircuitOutput
public import Human.ISA.RV32

@[expose] public section

/-! RV32 vocabulary for the SLT/SLTI/SLTU/SLTIU, branch and JAL/JALR circuit: register fields are `RV.Reg`, the pre-state is an `RV.State`, and the instruction is `RV.decode` of
    the public program entry. `Comparison.Opcode` and `Jump.Instruction` (encodings only) and `Circuit.Output`
    (destination word and PC) are the circuit-side types. -/

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

/-- Public conditions shared by comparisons, branches and jumps, in RV32 terms (no code-alignment premise: the
    program table's fetch guard, `rvProgramEntryWith`, aligns every PC). `terminalPC` stays: this circuit does not
    range-check the outgoing PC's high limb (column 17); a row's outgoing PC is canonical because it is the next
    row's incoming PC (a decoder-table PC) or, for the last row, the terminal PC. -/
structure RVTraceInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop
    extends RVPooledHistoryInputs trace initial cells program where
  /-- Both terminal-PC limbs are canonical 16-bit values; intermediate PCs are derived. -/
  terminalPC : trace.terminal.word.Bounded

end Airbender.JumpBranchSlt

namespace Airbender.JumpBranchSlt.Comparison
open Arithmetic Variables Trace

/-- The comparison's input in RV32 terms (`Input`); registers may alias. `right` is the second register word or the
    sign-extended immediate. -/
structure RVInput where
  opcode : Opcode
  left : Word
  right : Word
  pc : Word
  rs1 : RV.Reg
  rs2 : RV.Reg
  rd : RV.Reg
  encodedImmediate : BitVec 12
  /-- The row's pre-state. -/
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  match input.opcode with
  | .slt => .op .slt input.rd input.rs1 input.rs2
  | .slti => .opImm .slt input.rd input.rs1 (input.encodedImmediate.signExtend 32)
  | .sltu => .op .sltu input.rd input.rs1 input.rs2
  | .sltiu => .opImm .sltu input.rd input.rs1 (input.encodedImmediate.signExtend 32)

/-- `WordMapping` for the RV input: the same imported variables. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  leftLo : input.left.lo = (w rs1Lo).val
  leftHi : input.left.hi = (w rs1Hi).val
  rightLo : input.right.lo = (w rs2Lo + w immediateLo).val
  rightHi : input.right.hi = (w rs2Hi + w immediateHi).val
  rs1Index : w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  rs2Index : w Variables.rs2Index = (input.rs2.toNat : ZMod p)
  rdIndex : w Variables.rdIndex = (input.rd.toNat : ZMod p)
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  outputLo : output.destination.lo = (w destinationLo).val
  outputHi : output.destination.hi = (w destinationHi).val
  finalPCLo : output.pc.lo = (w finalPCLo).val
  finalPCHi : output.pc.hi = (w finalPCHi).val

/-- Trace mapping in RV32 terms: the row's pre-state is the RV state at its clock position, and its decoder entry in
    the public program is `RV.decode` of the entry's encoding, equal to the input's instruction. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand, register, destination and PC variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- The comparison's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w =>
    Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- Assumptions of the RV statements: `RVTraceInputs`. No code-alignment premise is needed. -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVTraceInputs trace initial cells program

end Airbender.JumpBranchSlt.Comparison

namespace Airbender.JumpBranchSlt.Branch
open Arithmetic Variables Trace

/-- The branch's input in RV32 terms: `cond` is the RV branch condition. -/
structure RVInput where
  cond : RV.Cond
  left : Word
  right : Word
  offset : Word
  pc : Word
  rs1 : RV.Reg
  rs2 : RV.Reg
  encodedOffset : BitVec 13
  /-- The row's pre-state. -/
  before : RV.State

/-- The RV32 instruction the row executes (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  .branch input.cond input.rs1 input.rs2 (input.encodedOffset.signExtend 32)

/-- `WordMapping` for the RV input: the same imported variables. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  leftLo : input.left.lo = (w rs1Lo).val
  leftHi : input.left.hi = (w rs1Hi).val
  rightLo : input.right.lo = (w rs2Lo).val
  rightHi : input.right.hi = (w rs2Hi).val
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  offsetLo : input.offset.lo = (w immediateLo).val
  offsetHi : input.offset.hi = (w immediateHi).val
  outputLo : output.destination.lo = (w destinationLo).val
  outputHi : output.destination.hi = (w destinationHi).val
  finalPCLo : output.pc.lo = (w finalPCLo).val
  finalPCHi : output.pc.hi = (w finalPCHi).val
  rs1Index : w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  rs2Index : w Variables.rs2Index = (input.rs2.toNat : ZMod p)

/-- Trace mapping in RV32 terms, as `Comparison.RVTraceMapping`. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand, register, destination and PC variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- The branch's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w =>
    Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- Assumptions of the RV statements: `RVTraceInputs`. No code-alignment premise is needed. -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVTraceInputs trace initial cells program

end Airbender.JumpBranchSlt.Branch

namespace Airbender.JumpBranchSlt.Jump
open Arithmetic Variables Trace

/-- The jump's input in RV32 terms (`Input`). -/
structure RVInput where
  instruction : Instruction
  source : Word
  offset : Word
  pc : Word
  rs1 : RV.Reg
  rd : RV.Reg
  /-- The row's pre-state. -/
  before : RV.State

/-- The target base: rs1's word for JALR, the PC for JAL (`Input.base`). -/
def RVInput.base (input : RVInput) : Word :=
  if input.instruction.indirect then input.source else input.pc

/-- The RV32 instruction the row executes (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  match input.instruction with
  | .jal offset => .jal input.rd (offset.signExtend 32)
  | .jalr offset => .jalr input.rd input.rs1 (offset.signExtend 32)

/-- `WordMapping` for the RV input: the same imported variables. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  baseLo : input.base.lo = (w (if input.instruction.indirect then rs1Lo else initialPCLo)).val
  baseHi : input.base.hi = (w (if input.instruction.indirect then rs1Hi else initialPCHi)).val
  offsetLo : input.offset.lo = (w immediateLo).val
  offsetHi : input.offset.hi = (w immediateHi).val
  outputLo : output.destination.lo = (w destinationLo).val
  outputHi : output.destination.hi = (w destinationHi).val
  finalPCLo : output.pc.lo = (w finalPCLo).val
  finalPCHi : output.pc.hi = (w finalPCHi).val
  rs1Index : input.instruction.indirect = true → w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  rdIndex : w Variables.rdIndex = (input.rd.toNat : ZMod p)

/-- Trace mapping in RV32 terms, as `Comparison.RVTraceMapping`. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand, register, destination and PC variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- The jump's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w =>
    Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- Assumptions of the RV statements: `RVTraceInputs`. No code-alignment premise is needed. -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVTraceInputs trace initial cells program

end Airbender.JumpBranchSlt.Jump
