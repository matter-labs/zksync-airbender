import Airbender.Proofs.Trace.Families.ShiftBinop.Clauses

namespace Airbender.ShiftBinop
set_option autoImplicit false
open Trace Reference.RiscV.Sail

/-- Original public bytes, initialization and accepted native matching/decoding
    derive actual GPR histories and original Sail clause execution for all six
    ordinary operations and immediate forms, retaining discarded x0 writes. -/
theorem public_clause_history {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ClauseHistory trace setup initial cells :=
  Proofs.image_clause_history image inputs accepted decoded aligned

end Airbender.ShiftBinop
