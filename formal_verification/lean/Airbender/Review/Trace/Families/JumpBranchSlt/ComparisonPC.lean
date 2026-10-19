import Airbender.Proofs.Trace.Families.JumpBranchSlt.ComparisonPC

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

/-- Every SLT/SLTU/SLTI/SLTIU row advances PC by four with RV32 wrap and
    four-byte alignment. Actual public decoding and native constraints derive
    bounds, selection and carries. Original Sail instruction retirement is separate. -/
theorem public_comparison_pc {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val ∈ [4,8] →
      let w := row.assignment
      (Word.mk (w 13).val (w 14).val).toBitVec =
        (Word.mk (w 0).val (w 1).val).toBitVec + 4 ∧
      (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 :=
  Proofs.image_comparison_pc image accepted decoded

end Airbender.JumpBranchSlt
