import Airbender.Review.Helpers.Memory.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.PC

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- Actual native row history executes the retained original instruction with
    original nextPC preparation/retirement and the exact native successor PC. -/
def ShiftRowExecution (row : Row mersenne31Modulus NativeReducedFamily) (entry : ShiftProgramEntry)
    (cells : List Cell) (epoch : Nat) : Prop :=
  (Word.mk (row.assignment 13).val (row.assignment 14).val).Bounded ∧
  ∀ before after : State, SailHistory cells (rowEvents epoch row).reverse before after →
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause)
        (retiredState before (Word.mk (row.assignment 0).val (row.assignment 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (row.assignment 13).val (row.assignment 14).val).toBitVec)

/-- Constructed actual GPR segment states plus original local retired steps.
    Complete fetched execution is assembled separately. -/
def ShiftInstructionHistory (trace : Data mersenne31Modulus NativeReducedFamily)
    (setup : SparseDecoderSetup ShiftMode) (initial : State) (cells : List Cell) : Prop :=
  ShiftRegisterHistory trace setup initial cells ∧
  ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
    entry.SourceWith initial shiftDecoderFields ∧ row.decoderQuery = entry.query ∧
      ShiftRowExecution row entry cells trace.memoryEpoch

end Airbender.ReducedMachine.Native
