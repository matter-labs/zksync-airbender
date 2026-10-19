import Airbender.Proofs.Trace.Families.MulDiv.Composition

namespace Airbender.MulDiv
open Trace Reference.RiscV.Sail

/-- Original fetched unsigned MUL/DIV instructions form a finite Sail execution
    from actual public initialization to native terminal PC and register values. -/
theorem public_execution {trace : Data mersenne31Modulus MulDivFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    trace.terminal.word.Bounded ∧
      Realizes (StepWith decoderFields registerClause setup.program) trace initial cells :=
  ⟨Proofs.image_terminal_pc_bound image inputs.initial accepted decoded,
    Proofs.image_execution_soundness image inputs accepted decoded aligned⟩

end Airbender.MulDiv
