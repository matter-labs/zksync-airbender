import Airbender.Review.Helpers.Memory.MulDiv
import Airbender.Review.Circuits.MulDiv.Sail

namespace Airbender.MulDiv
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- Each native row executes its decoded original clause from the actual cell
    history, with original preparation/retirement and the actual successor PC. -/
def RowExecution {p : Nat} (row : Row p MulDivFamily) (entry : ProgramEntry)
    (cells : List Cell) (epoch : Nat) : Prop :=
  entry.instruction = instruction entry.data.family entry.data.rs1 entry.data.rs2 entry.data.rd ∧
  (Word.mk (row.assignment 13).val (row.assignment 14).val).Bounded ∧
  ∀ before after, SailHistory cells (rowEvents epoch row).reverse before after →
    run (normalStep (clause entry.data.family entry.data.rs1 entry.data.rs2 entry.data.rd))
      (retiredState before (Word.mk (row.assignment 0).val (row.assignment 1).val).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (Word.mk (row.assignment 13).val (row.assignment 14).val).toBitVec)

/-- Constructed real segment states and original local instruction steps.
    Composition with fetch across the complete trace is a separate claim. -/
def InstructionHistory {p : Nat} [Fact p.Prime] (trace : Data p MulDivFamily)
    (setup : SparseDecoderSetup Operation) (initial : State) (cells : List Cell) : Prop :=
  RegisterHistory trace setup initial cells ∧
  ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
    entry.SourceWith initial decoderFields ∧ row.decoderQuery = entry.query ∧
      RowExecution row entry cells trace.memoryEpoch

end Airbender.MulDiv
