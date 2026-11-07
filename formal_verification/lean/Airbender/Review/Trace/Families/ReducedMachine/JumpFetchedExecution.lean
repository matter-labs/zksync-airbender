import Airbender.Proofs.Trace.Families.ReducedMachine.JumpComposition

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Original fetched JAL/JALR execute from public initialization to actual
    terminal PC/cells. Initial CSR configuration is conditional on the public
    program; every local read/range/state/replay is derived. Physical/protocol/
    setup and original interrupt/exception paths stay separate. -/
theorem public_jump_execution {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup JumpMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : jumpDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : JumpDecodedTrace (fixedData trace) setup)
    (isa : JumpISA setup initial)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (fixedData trace).terminal.word.Bounded ∧
      Realizes (StepWith jumpDecoderFields registerClause setup.program) (fixedData trace) initial cells :=
  ⟨NativeJumpExecutionProofs.image_terminal_pc_bound image inputs accepted decoded,
    NativeJumpExecutionProofs.image_execution_soundness image inputs accepted decoded isa aligned⟩

end Airbender.ReducedMachine.Native
