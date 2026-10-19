import Airbender.Proofs.Trace.Families.JumpBranchSlt.BranchExecution

namespace Airbender.JumpBranchSlt
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- All six original branches prepare and retire to native targets in
    constructed initialized-history segments. The public misa value is
    unrestricted and transported through history. Full fetched composition is separate. -/
theorem public_branch_execution {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup)
    (isa : ∃ value, before.regs.get? .misa = some value) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus JumpBranchSltFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after ∧
      ∀ newer row older, rows = newer ++ row :: older → (row.assignment 12).val = 16 →
        ∃ entry ∈ setup.program, ∃ rowBefore rowAfter clause,
          entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query ∧
          SailHistory cells (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before rowBefore ∧
          SailHistory cells (rowEvents trace.memoryEpoch row).reverse rowBefore rowAfter ∧
          SailHistory cells (newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) rowAfter after ∧
          registerClause entry.instruction = some clause ∧
          run (normalStep clause)
            (retiredState rowBefore (Word.mk (row.assignment 0).val (row.assignment 1).val).toBitVec) =
            .ok SailRV32.Functions.RETIRE_SUCCESS
              (retiredState rowAfter (Word.mk (row.assignment 13).val (row.assignment 14).val).toBitVec) :=
  Proofs.image_branch_execution image inputs accepted decoded isa aligned

end Airbender.JumpBranchSlt
