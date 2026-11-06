import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticRegisterHistory

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Public bytes/decoding, seed reads and accepted actual native matching derive
    every original Sail GPR observation/write and instruction segment state,
    preserved code/misa and final cell matching. No per-row read, state or result
    is supplied. Original executed clauses, PC and physical setup remain separate. -/
theorem public_arithmetic_register_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ArithmeticRegisterHistory trace setup initial cells :=
  NativeArithmeticRegisterProofs.image_register_history image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
