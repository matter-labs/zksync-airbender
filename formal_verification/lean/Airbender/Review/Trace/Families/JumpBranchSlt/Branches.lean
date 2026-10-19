import Airbender.Proofs.Trace.Families.JumpBranchSlt.Branches

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

/-- All six original branch conditions and both native routing bits follow from
    public decoding and initialized matching. Actual unused writes are zero.
    No operand bound, equality/sign/borrow bit or desired condition is supplied.
    Branch PC targets and original Sail execution/retirement remain separate. -/
theorem public_branches {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val = 16 →
      let w := row.assignment
      let taken := branchCondition (w 11).val (Word.mk (w 22).val (w 23).val)
        (Word.mk (w 24).val (w 25).val)
      (w 46).val = (if taken then 1 else 0) ∧
      (w 45).val = (if taken then 0 else 1) ∧
      (Word.mk (w 38).val (w 39).val).value = 0 :=
  Proofs.image_branches image inputs accepted decoded

end Airbender.JumpBranchSlt
