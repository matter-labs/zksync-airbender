import Airbender.Proofs.Trace.Families.ReducedMachine.Clauses

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Original public bytes/decoding, seed reads and accepted actual native matching
    derive GPR histories and retained original Sail shift clause execution. Source
    ranges, selected operands and actual writes are derived, including x0. Native
    PC preparation/retirement, fetched execution and physical setup remain separate. -/
theorem public_shift_clause_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ShiftClauseHistory (fixedData trace) setup initial cells :=
  NativeShiftClauseProofs.image_clause_history image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
