import Airbender.Proofs.Trace.Families.ReducedMachine.SupportedExecution

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Original fetched mixed selected native reduced shift/arithmetic/bitwise instructions form a finite Sail execution
    from actual public initialization to native terminal PC and register values.
    Other combined profiles, native physical setup/protocol/terminal enforcement
    and compiler/cryptographic/completeness boundaries remain separate. -/
theorem public_supported_execution {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup SupportedMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace)) (decoded : SupportedDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (fixedData trace).terminal.word.Bounded ∧
      Realizes (StepWith supportedDecoderFields registerClause setup.program) (fixedData trace) initial cells :=
  ⟨NativeSupportedExecutionProofs.image_terminal_pc_bound image inputs.initial accepted decoded,
    NativeSupportedExecutionProofs.image_execution_soundness image inputs accepted decoded aligned⟩

end Airbender.ReducedMachine.Native
