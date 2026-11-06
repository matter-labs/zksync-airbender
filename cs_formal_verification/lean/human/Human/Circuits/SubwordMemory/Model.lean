import Human.Helpers.Decoder.Instruction
import Human.Circuits.SubwordMemory.Artifact
import Human.Helpers.Context.Interfaces
import Human.Helpers.Core.Sail
import Human.Helpers.Properties
import Human.Helpers.Decoder.PooledProgram
import Human.Helpers.Context.RowContext

namespace Airbender.SubwordMemory
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem
open Trace

/-- Original load/store operands and native pre-state. `readData` is the aligned
    RAM word on loads, rs2 on stores and unused on ROM; `oldData` is the cell before a store. -/
structure Input where
  store : Bool
  byte : Bool
  signed : Bool
  source : Word
  immediate : Word
  readData : Word
  oldData : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  encodedImmediate : BitVec 12
  before : Sail.State

structure Output where
  cell : Word
  data : Word
  pc : Word


/-- Original Sail constructor used by both public-program binding and execution. -/
def instruction (input : Input) : SailRV32.instruction :=
  if input.store then
    .STORE (input.encodedImmediate, input.rs2, input.rs1, if input.byte then 1 else 2)
  else .LOAD (input.encodedImmediate, input.rs1, input.rd, !input.signed,
    if input.byte then 1 else 2)

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  (instructionClause (instruction input)).get (by cases h_store : input.store <;> cases h_byte : input.byte <;> simp_all [instruction, instructionClause])

/-- Correct aligned cell address and complete native effects: loads write rd,
    stores write the merged cell and preserve GPRs. Sail supplies the ISA behavior. -/
def spec (input : Input) (output : Output) : Prop :=
  output.cell.toBitVec.toNat =
    (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
  if input.store then
    Sail.stepSpec input.before (execution input) Sail.zeroRegister ⟨⟨0, 0⟩, output.pc⟩
      (Sail.writeMemory (size := 4) output.cell.toBitVec output.data.toBitVec)
  else Sail.stepSpec input.before (execution input) input.rd ⟨output.data, output.pc⟩

/-- Canonical imported operand, cell, register, result and PC variables.
    Native ROM shadow data and the public byte image are separate. -/
structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  sourceLo : input.source.lo = (w 19).val
  sourceHi : input.source.hi = (w 20).val
  immediateLo : input.immediate.lo = (w 8).val
  immediateHi : input.immediate.hi = (w 9).val
  readLo : input.readData.lo = (w 25).val
  readHi : input.readData.hi = (w 26).val
  oldLo : input.store = true → input.oldData.lo = (w 31).val
  oldHi : input.store = true → input.oldData.hi = (w 32).val
  cellLo : output.cell.lo = (if input.store then w 27 else w 21).val
  cellHi : output.cell.hi = (if input.store then w 28 else w 22).val
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.data.lo = (w 33).val
  outputHi : output.data.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

/-- Interpret one subword assignment at its shared-history position.
    `initial` supplies public Sail state, `cells` names tracked registers/RAM,
    and `program` is bound to actual public byte decoding by initialization. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  /-- Name imported operands, cell address, registers, merged/result word and PCs. -/
  words : WordMapping input output w
  /-- Build `input.before` from earlier native writes and this row's start PC;
      actual reads and bounds follow from initialized history. -/
  state : RowPosition trace initial cells ⟨.subwordMemory, w⟩ input.before
  /-- Match the row query to the public instruction's original Sail constructor.
      Width/sign identify the instruction; no execution result is assumed. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .subwordMemory ∧
    (⟨.subwordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    entry.instruction = instruction input

def circuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ PooledDecoded trace program ∧ (⟨.subwordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public history/table binding and the ordinary Sail memory configuration.
    Shared history derives operand/address bounds, reads and memory transport.
    Public ROM bytes remain tied to the initial state, separately from shadow tokens. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) : Prop
    extends PooledHistoryInputs trace initial cells program where
  ordinary : ∀ address, Cell.ram address ∈ cells → Sail.OrdinaryWordAddress address
  configuration : Sail.Configured initial

end Airbender.SubwordMemory
