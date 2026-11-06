import Airbender.Proofs.Trace.Families.ReducedMachine.RegisterHistory
import Airbender.Review.Trace.Families.ReducedMachine.FixedData

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Public bytes/decoding, seed reads and accepted actual native matching derive
    every original Sail GPR observation/write and instruction segment state,
    preserved code/misa and final cell matching. No per-row read, state or result
    is supplied. Original executed clauses, PC and physical setup remain separate. -/
theorem public_shift_register_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ShiftRegisterHistory (fixedData trace) setup initial cells :=
  NativeShiftRegisterProofs.image_register_history image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
