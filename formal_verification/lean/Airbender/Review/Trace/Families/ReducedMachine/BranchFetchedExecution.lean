import Airbender.Proofs.Trace.Families.ReducedMachine.BranchComposition

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Original fetched native branches execute from public initialization to actual
    terminal PC/cells. Misa readability is a public Sail configuration boundary;
    its value is unrestricted and each local read is derived through history.
    Native physical/protocol/setup and interrupt/exception scopes stay separate. -/
theorem public_branch_execution {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : BranchDecodedTrace (fixedData trace) setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (fixedData trace).terminal.word.Bounded ∧
      Realizes (StepWith branchDecoderFields registerClause setup.program) (fixedData trace) initial cells :=
  ⟨NativeBranchExecutionProofs.image_terminal_pc_bound image inputs accepted decoded,
    NativeBranchExecutionProofs.image_execution_soundness image inputs accepted decoded isa aligned⟩

end Airbender.ReducedMachine.Native
