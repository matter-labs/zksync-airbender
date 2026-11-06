import Airbender.Review.Helpers.Memory.ReducedMachine

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail Reference.Sail
set_option autoImplicit false

/-- Retained original Sail clause execution on actual native row history.
    Preparation/retirement, numerical PC and fetched execution are separate. -/
def ShiftClauseExecution (row : Row mersenne31Modulus NativeReducedFamily)
    (entry : ShiftProgramEntry) (cells : List Cell) (epoch : Nat) : Prop :=
  ∀ before after : State, SailHistory cells (rowEvents epoch row).reverse before after →
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after

/-- Initialized original GPR histories plus original clauses for every selected
    native shift. Source bounds, selected operands and actual results are derived. -/
def ShiftClauseHistory (trace : Data mersenne31Modulus NativeReducedFamily)
    (setup : SparseDecoderSetup ShiftMode) (initial : State) (cells : List Cell) : Prop :=
  ShiftRegisterHistory trace setup initial cells ∧
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith initial shiftDecoderFields ∧ row.decoderQuery = entry.query ∧
      ShiftClauseExecution row entry cells trace.memoryEpoch

end Airbender.ReducedMachine.Native
