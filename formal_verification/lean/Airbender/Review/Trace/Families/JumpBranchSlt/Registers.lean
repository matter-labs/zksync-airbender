import Airbender.Proofs.Trace.Families.JumpBranchSlt.RegisterHistory

namespace Airbender.JumpBranchSlt
open Trace Reference.RiscV.Sail Reference.Sail

/-- Actual public bytes/decoding and initialized native matching derive every
    original source/destination register read and actual masked write in clock
    order. All three reads use the same instruction pre-state, including aliases.
    Segment states are constructed. Original instruction/PC execution is separate. -/
theorem public_register_history {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus JumpBranchSltFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
        before after ∧ SailStateMatches cells history after ∧
      ∀ newer row older, rows = newer ++ row :: older →
        ∃ entry ∈ setup.program, ∃ rowBefore rowAfter,
          entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query ∧
          SailHistory cells (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
            before rowBefore ∧
          SailHistory cells (rowEvents trace.memoryEpoch row).reverse rowBefore rowAfter ∧
          SailHistory cells (newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
            rowAfter after ∧
          run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) rowBefore =
            .ok (memoryWord (importedConstraintsMemoryPorts[0].readCode row.assignment)) rowBefore ∧
          run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) rowBefore =
            .ok (memoryWord (importedConstraintsMemoryPorts[1].readCode row.assignment)) rowBefore ∧
          run (SailRV32.Functions.rX_bits (.Regidx entry.data.rd)) rowBefore =
            .ok (memoryWord (importedConstraintsMemoryPorts[2].readCode row.assignment)) rowBefore ∧
          run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
            (memoryWord (importedConstraintsMemoryPorts[2].writeCode row.assignment))) rowBefore =
            .ok () rowAfter :=
  Proofs.image_register_history image inputs accepted decoded aligned

end Airbender.JumpBranchSlt
