import Airbender.Proofs.Trace.Families.JumpBranchSlt.BranchTargets

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

/-- All six initialized branch conditions select PC+offset or PC+4, with
    RV32 wrap and four-byte alignment. Bounds, parity, selectors and carries
    are derived. Original Sail clauses and retirement remain separate. -/
theorem public_branch_targets {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val = 16 →
      let w := row.assignment
      let pc := (Word.mk (w 0).val (w 1).val).toBitVec
      let offset := (Word.mk (w 9).val (w 10).val).toBitVec
      let taken := branchCondition (w 11).val (Word.mk (w 22).val (w 23).val)
        (Word.mk (w 24).val (w 25).val)
      (Word.mk (w 13).val (w 14).val).toBitVec = (if taken then pc+offset else pc+4) ∧
      (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 :=
  Proofs.image_branch_targets image inputs accepted decoded

end Airbender.JumpBranchSlt
