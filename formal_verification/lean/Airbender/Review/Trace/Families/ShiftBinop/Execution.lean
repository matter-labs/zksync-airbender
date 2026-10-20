import Airbender.Proofs.Trace.Families.ShiftBinop.Execution

namespace Airbender.ShiftBinop
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Actual public initialization and accepted native matching yield constructed
    register histories and original local instruction preparation/retirement. -/
theorem public_instruction_history {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    InstructionHistory trace setup initial cells :=
  Proofs.image_instruction_history image inputs accepted decoded aligned

end Airbender.ShiftBinop
