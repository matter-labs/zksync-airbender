import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticExecution

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Actual public initialization and accepted native matching yield constructed
    register histories and original local instruction preparation/retirement. -/
theorem public_arithmetic_instruction_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ArithmeticInstructionHistory trace setup initial cells :=
  NativeArithmeticExecutionProofs.image_instruction_history image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
