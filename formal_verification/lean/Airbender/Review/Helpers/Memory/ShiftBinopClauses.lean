import Airbender.Review.Helpers.Memory.ShiftBinop

namespace Airbender.ShiftBinop
set_option autoImplicit false
open Trace Reference.RiscV.Sail Reference.Sail

/-- Original pinned clause execution on the actual native row history. The
    original instruction and actual states are retained, including x0 forms.
    PC preparation/retirement and fetched execution are separate. -/
def ClauseExecution {p : Nat} (row : Row p ShiftBinopFamily) (entry : ProgramEntry)
    (cells : List Cell) (epoch : Nat) : Prop :=
  ∀ before after : State, SailHistory cells (rowEvents epoch row).reverse before after →
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after

/-- Initialized GPR histories plus original clause execution for every decoded
    native row. The public theorem derives all source reads, bounds and states. -/
def ClauseHistory {p : Nat} [Fact p.Prime] (trace : Data p ShiftBinopFamily)
    (setup : SparseDecoderSetup Operation) (initial : State) (cells : List Cell) : Prop :=
  RegisterHistory trace setup initial cells ∧
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith initial decoderFields ∧ row.decoderQuery = entry.query ∧
      ClauseExecution row entry cells trace.memoryEpoch

end Airbender.ShiftBinop
