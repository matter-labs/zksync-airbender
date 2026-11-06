import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticComposition

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Original fetched native reduced arithmetic instructions form a finite Sail execution
    from actual public initialization to native terminal PC and register values.
    Other combined profiles, native physical setup/protocol/terminal enforcement
    and compiler/cryptographic/completeness boundaries remain separate. -/
theorem public_arithmetic_execution {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : ArithmeticDecodedTrace trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    trace.terminal.word.Bounded ∧
      Realizes (StepWith arithmeticDecoderFields registerClause setup.program) trace initial cells :=
  ⟨NativeArithmeticExecutionProofs.image_terminal_pc_bound image inputs.initial accepted decoded,
    NativeArithmeticExecutionProofs.image_execution_soundness image inputs accepted decoded aligned⟩

end Airbender.ReducedMachine.Native
