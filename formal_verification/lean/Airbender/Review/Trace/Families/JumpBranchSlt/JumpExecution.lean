import Airbender.Proofs.Trace.Families.JumpBranchSlt.JumpExecution

namespace Airbender.JumpBranchSlt
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- Original JAL/JALR clauses retire to native targets and actual masked
    link writes in constructed history segments. Public misa is readable;
    traces containing JALR use Machine mode with MLPE clear. Full fetched
    composition is separate. -/
theorem public_jump_execution {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup)
    (isa : ∃ value, before.regs.get? .misa = some value)
    (configuration : (∃ row ∈ trace.rows, (row.assignment 12).val = 2) →
      before.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
        before.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus JumpBranchSltFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after ∧
      ∀ newer row older, rows = newer ++ row :: older → (row.assignment 12).val ∈ [1,2] →
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
  Proofs.image_jump_execution image inputs accepted decoded isa configuration aligned

end Airbender.JumpBranchSlt
