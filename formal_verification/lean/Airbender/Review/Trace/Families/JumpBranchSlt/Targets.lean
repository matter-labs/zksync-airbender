import Airbender.Proofs.Trace.Families.JumpBranchSlt.Targets

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

/-- Every JAL/JALR target and its alignment follow from native acceptance,
    initialized matching and actual public byte decoding. No operand bound,
    selector, parity, carry or expected target is supplied. Original instruction
    execution and PC retirement remain separate. -/
theorem public_jump_targets {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, (row.assignment 12).val ∈ [1,2] →
      let w := row.assignment
      let base := Word.mk (w (if (w 12).val = 2 then 22 else 0)).val
        (w (if (w 12).val = 2 then 23 else 1)).val
      let sum := base.toBitVec + (Word.mk (w 9).val (w 10).val).toBitVec
      (Word.mk (w 13).val (w 14).val).toBitVec =
        (if (w 12).val = 2 then sum &&& 0xfffffffe else sum) ∧
      (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 :=
  Proofs.image_jump_targets image inputs accepted decoded

end Airbender.JumpBranchSlt
