import Airbender.Proofs.Trace.Families.JumpBranchSlt.Comparisons

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

/-- Actual initialized native SLT/SLTU/SLTI/SLTIU masked results. Public decoding
    fixes signedness, immediate choice and x0; matching derives operand ranges.
    No selector, sign/borrow bit, operand bound or desired result is supplied.
    Original Sail instruction execution and PC retirement remain separate. -/
theorem public_comparisons {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val ∈ [4,8] →
      let w := row.assignment
      let left := Word.mk (w 22).val (w 23).val
      let right := Word.mk (w (if (w 12).val = 8 then 9 else 24)).val
        (w (if (w 12).val = 8 then 10 else 25)).val
      (Word.mk (w 38).val (w 39).val).value =
        if (w 7).val = 0 then 0 else
        if (w 11).val = 2 then (if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0)
        else (if left.value < right.value then 1 else 0) :=
  Proofs.image_comparisons image inputs accepted decoded

end Airbender.JumpBranchSlt
