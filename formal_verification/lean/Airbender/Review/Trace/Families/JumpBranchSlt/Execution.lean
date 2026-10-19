import Airbender.Proofs.Trace.Families.JumpBranchSlt.Composition

namespace Airbender.JumpBranchSlt
open Trace Reference.RiscV.Sail

/-- Original fetched control instructions form a finite Sail execution from
    public initialization to actual native terminal PC/register values. The
    initial ISA entry and JALR Machine/MLPE-clear profile remain explicit. -/
theorem public_execution {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : (∃ row ∈ trace.rows, (row.assignment 12).val = 2) →
      initial.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
        initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    trace.terminal.word.Bounded ∧
      Realizes (StepWith decoderFields registerClause setup.program) trace initial cells :=
  ⟨Proofs.image_terminal_pc_bound image inputs accepted decoded,
    Proofs.image_execution_soundness image inputs accepted decoded isa configuration aligned⟩

end Airbender.JumpBranchSlt
