import Airbender.Proofs.Trace.Families.ReducedMachine.JumpRegisterHistory

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Public bytes/decoding, seed reads and accepted actual native matching derive
    every original Sail GPR observation/write and instruction segment state,
    preserved code/misa and final cell matching. No per-row read, state or result
    is supplied. Original executed clauses, PC and physical setup remain separate. -/
theorem public_jump_register_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup JumpMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : jumpDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : JumpDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    JumpRegisterHistory trace setup initial cells :=
  NativeJumpRegisterProofs.image_register_history image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
