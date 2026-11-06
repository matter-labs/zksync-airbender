import Human.Helpers.Context.Boundary
import Human.Circuits.UnifiedReduced.TriAdd

namespace Airbender.UnifiedReduced.XorRotate
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace

/-- MOP.R.16/12/8/7 from the pinned project spec. The same index selects
    the native table tag and the word rotation; no witness chooses the operation. -/
def amount (rotation : Fin 4) : Nat := #[16, 12, 8, 7][rotation.val]!

structure Input where
  rotation : Fin 4
  left : Word
  oldDestination : Word
  rs1 : SailRV32.regidx
  rd : SailRV32.regidx
  pc : Word
  before : State

/-- Project XORROT: read rs1 and old rd, write their XOR rotated right,
    then retire through Sail's native register and PC machinery. -/
def clause (rotation : Nat) (rs1 rd : SailRV32.regidx) : SailRV32.SailM SailRV32.ExecutionResult := do
  let left ← SailRV32.Functions.rX_bits rs1
  let old ← SailRV32.Functions.rX_bits rd
  SailRV32.Functions.wX_bits rd ((left ^^^ old).rotateRight rotation)
  pure SailRV32.Functions.RETIRE_SUCCESS

abbrev execution (input : Input) := clause (amount input.rotation) input.rs1 input.rd

abbrev spec (input : Input) (output : Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- The original Sail MOP constructor. Public decoding fixes the rotation
    and both register indices before native selectors and reads are derived. -/
noncomputable def instruction (input : Input) : SailRV32.instruction :=
  .ZIMOP_MOP_R (BitVec.ofNat 5 (amount input.rotation), input.rs1, input.rd)

/-- Bind only observable words. The second native read is old rd, since
    original custom decoding sets rs2 = rd. Bounds and read values are proved. -/
structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  left : input.left = TriAdd.leftOperand w
  oldDestination : input.oldDestination = TriAdd.rightOperand w
  pc : input.pc = Control.initialPC w
  destination : output.destination = Control.destination w
  finalPC : output.pc = Control.finalPC w

/-- Locate this row in initialized history and the actual decoded public
    program. `state` applies older writes; `instruction` identifies the case. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
    entry.instruction = XorRotate.instruction input

/-- Full imported richer constraints, actual decoder membership and shared
    logical matching, interpreted by the named native observations above. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public initialization, clocks, actual decoding and the current modeled
    pooled table. History and lookup equations derive operands, bounds,
    selectors and results. No per-row range or desired read is a premise. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (_input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs customDecoderFields trace initial cells program
  setup : trace.rom = Setup.table initial

end Airbender.UnifiedReduced.XorRotate
