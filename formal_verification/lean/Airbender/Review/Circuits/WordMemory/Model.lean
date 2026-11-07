import Airbender.Review.Helpers.Decoder.Instruction
import Airbender.Review.Circuits.WordMemory.Artifact
import Airbender.Review.Helpers.Core.Sail
import Airbender.Review.Helpers.Properties
import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Helpers.Context.RowContext
import Airbender.Review.Helpers.Context.Interfaces

namespace Airbender.WordMemory
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem Variables Trace

/-- Fixed pre-state and decoded LW/SW operands. `readData` is the read-port word:
    RAM on LW, rs2 on SW, and an unused placeholder on ROM loads. -/
structure Input where
  store : Bool
  source : Word
  immediate : Word
  readData : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  encodedImmediate : BitVec 12
  before : Sail.State

structure Output where
  address : Word
  data : Word
  pc : Word

variable [MemoryPlatform SailRV32.exception]

/-- Original Sail constructor used by both public-program binding and execution. -/
def instruction (input : Input) : SailRV32.instruction :=
  if input.store then
    .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
  else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  (instructionClause (instruction input)).get (by cases h_store : input.store <;> simp_all [instruction, instructionClause])

/-- Address correctness plus agreement of the complete native state/PC effects.
    Stores project a native memory write and leave GPRs unchanged; loads use rd. -/
def spec (input : Input) (output : Output) : Prop :=
  output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec ∧
  if input.store then
    Sail.stepSpec input.before (execution input) Sail.zeroRegister ⟨⟨0, 0⟩, output.pc⟩
      (Sail.writeMemory (size := 4) output.address.toBitVec output.data.toBitVec)
  else Sail.stepSpec input.before (execution input) input.rd ⟨output.data, output.pc⟩

omit [MemoryPlatform SailRV32.exception] in
/-- Canonical input/output interpretation of the imported LW/SW variables. -/
structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  sourceLo : input.source.lo = (w Variables.sourceLo).val
  sourceHi : input.source.hi = (w Variables.sourceHi).val
  immediateLo : input.immediate.lo = (w Variables.immediateLo).val
  immediateHi : input.immediate.hi = (w Variables.immediateHi).val
  readLo : input.readData.lo = (w readDataLo).val
  readHi : input.readData.hi = (w readDataHi).val
  addressLo : output.address.lo = (w (if input.store then writeAddressLo else readAddressLo)).val
  addressHi : output.address.hi = (w (if input.store then writeAddressHi else readAddressHi)).val
  rs1Index : match input.rs1 with | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w Variables.rs2Index = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w Variables.rdIndex = (bits.toNat : ZMod p)
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  outputLo : output.data.lo = (w writeDataLo).val
  outputHi : output.data.hi = (w writeDataHi).val
  finalPCLo : output.pc.lo = (w Variables.finalPCLo).val
  finalPCHi : output.pc.hi = (w Variables.finalPCHi).val

omit [MemoryPlatform SailRV32.exception] in
/-- Interpret one LW/SW assignment in the shared trace. The public initial state
    and program are bound by `InterfaceAssumptions.initialization`; imported
    constraints and logical matching are checked by `circuitModel.satisfies`. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  /-- Name the operands, address, transferred data and PCs using the imported variables. -/
  words : WordMapping input output w
  /-- Obtain the pre-state from earlier register/RAM writes and this row's start PC.
      Successful reads and bounds are derived by the soundness proof. -/
  state : RowPosition trace initial cells ⟨.wordMemory, w⟩ input.before
  /-- Match the native decoder query to the original public Sail LOAD/STORE constructor. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .wordMemory ∧
    (⟨.wordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    entry.instruction = instruction input

omit [MemoryPlatform SailRV32.exception] in
def circuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ PooledDecoded trace program ∧ (⟨.wordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

omit [MemoryPlatform SailRV32.exception] in
/-- Public initialization, modeled tables and the ordinary flat-memory platform.
    Operand/address bounds, decoder preprocessing and successful register/memory
    transfers are proved internally. Logical matching and table membership retain
    their existing trust boundaries. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) : Prop
    extends PooledHistoryInputs trace initial cells program where
  ordinary : ∀ address, Cell.ram address ∈ cells → Sail.PlatformWordAddress address
  configuration : Sail.FlatMemoryConfiguration initial

end Airbender.WordMemory
