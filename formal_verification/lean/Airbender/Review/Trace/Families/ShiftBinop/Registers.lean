import Airbender.Proofs.Trace.Families.ShiftBinop.RegisterHistory

namespace Airbender.ShiftBinop
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Actual public bytes/decoding, seed reads and accepted native matching derive
    original Sail GPR reads/writes, all segment states, preserved code/misa and
    final cell matching. No row read, state, result or decoder replay is supplied. -/
theorem public_register_history {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    RegisterHistory trace setup initial cells :=
  Proofs.image_register_history image inputs accepted decoded aligned

end Airbender.ShiftBinop
