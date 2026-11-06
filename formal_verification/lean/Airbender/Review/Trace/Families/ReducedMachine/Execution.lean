import Airbender.Proofs.Trace.Families.ReducedMachine.Execution

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Actual public initialization and accepted native matching yield constructed
    register histories and original local instruction preparation/retirement. -/
theorem public_shift_instruction_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ShiftInstructionHistory (fixedData trace) setup initial cells :=
  NativeShiftExecutionProofs.image_instruction_history image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
