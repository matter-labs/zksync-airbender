import Airbender.Proofs.Trace.Families.ReducedMachine.Composition

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Original fetched selected native reduced shift instructions form a finite Sail execution
    from actual public initialization to native terminal PC and register values.
    Other combined profiles, native physical setup/protocol/terminal enforcement
    and compiler/cryptographic/completeness boundaries remain separate. -/
theorem public_shift_execution {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace)) (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    trace.terminal.word.Bounded ∧
      Realizes (StepWith shiftDecoderFields registerClause setup.program) (fixedData trace) initial cells :=
  ⟨NativeShiftExecutionProofs.image_terminal_pc_bound image inputs.initial accepted decoded,
    NativeShiftExecutionProofs.image_execution_soundness image inputs accepted decoded aligned⟩

end Airbender.ReducedMachine.Native
