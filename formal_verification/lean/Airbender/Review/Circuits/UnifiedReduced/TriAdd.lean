import Airbender.Review.Helpers.Boundary
import Airbender.Review.Circuits.UnifiedReduced.Artifact
import Airbender.Review.Helpers.Properties
import Airbender.Review.Helpers.Sail
import Airbender.Review.Circuits.UnifiedReduced.Control
import Airbender.Review.Helpers.RowContext

namespace Airbender.UnifiedReduced.TriAdd
open Airbender.Reference.RiscV
open Airbender.Reference.Sail
open Airbender.Arithmetic

structure Input where
  left : Word
  right : Word
  oldDestination : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  pc : Word
  before : Sail.State

/-- MOP.RR.4 from vendor/airbender/00-master.md: rd_old + rs1 + rs2 modulo
    2^32. This is a project operation, using Sail's native register effects. -/
def clause (rs1 rs2 rd : SailRV32.regidx) : SailRV32.SailM SailRV32.ExecutionResult := do
  let left ← SailRV32.Functions.rX_bits rs1
  let right ← SailRV32.Functions.rX_bits rs2
  let old ← SailRV32.Functions.rX_bits rd
  SailRV32.Functions.wX_bits rd (old + left + right)
  pure SailRV32.Functions.RETIRE_SUCCESS

abbrev execution (input : Input) := clause input.rs1 input.rs2 input.rd

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Native source words, read from the imported port descriptors. No variable
    numbers or operand bounds are supplied by this interpretation. -/
def leftOperand (w : Nat → ZMod p) : Word :=
  (Trace.readToken w importedConstraintsMemoryPorts[0]).word

def rightOperand (w : Nat → ZMod p) : Word :=
  (Trace.readToken w importedConstraintsMemoryPorts[1]).word

/-- The third port reads rd before it is overwritten, including aliases with
    rs1 or rs2. Initialized history proves which value this observation contains. -/
def oldDestination (w : Nat → ZMod p) : Word :=
  (Trace.readToken w importedConstraintsMemoryPorts[2]).word

/-- Identify the declared words using actual native observations. This mapping
    says which words the theorem discusses; it assumes no bounds or behavior. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  /-- Canonical operands of the first and second native read ports. -/
  left : input.left = leftOperand w
  right : input.right = rightOperand w
  /-- Canonical old rd value from the third port. -/
  oldDestination : input.oldDestination = TriAdd.oldDestination w
  /-- Starting PC and native destination/final-PC observations. -/
  pc : input.pc = (⟨.machine, w⟩ : Trace.Row p Trace.UnifiedFamily).start.word
  destination : output.destination = Control.destination w
  finalPC : output.pc = Control.finalPC w

/-- Locate this TRIADD row in the initialized native history. Public instruction
    identity binds rs1, rs2 and rd to original Sail MOP.RR.4 decoding. `state`
    applies older native writes; actual reads and bounds are proved separately. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : Trace.UnifiedTrace p)
    (initial : Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry)
    (input : Input) (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  /-- Named native word observations, kept separate from history interpretation. -/
  words : WordMapping input output w
  /-- The input state belongs to this row in the actual initialized trace. -/
  state : Trace.RowPosition trace initial cells ⟨.machine, w⟩ input.before
  /-- This case is the original decoded MOP.RR.4 instruction, with its real indices. -/
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
    entry.instruction = .ZIMOP_MOP_RR (4, input.rs2, input.rs1, input.rd)

/-- The actual imported circuit and native logical matching. Other custom
    rows can share the history; this interpretation identifies one TRIADD row. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : Trace.UnifiedTrace p)
    (initial : Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => Trace.Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Trace.Row p Trace.UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public initialization, actual program decoding and initial clock conditions.
    Shared native history derives all three operands' ranges and successful
    reads, including the old destination. No selector, read or result is assumed. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : Trace.UnifiedTrace p)
    (initial : Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry)
    (_input : Input) (_output : Sail.Output) (_w : Nat → ZMod p) : Prop where
  initialization : Trace.NativeInputs customDecoderFields trace initial cells program

end Airbender.UnifiedReduced.TriAdd
