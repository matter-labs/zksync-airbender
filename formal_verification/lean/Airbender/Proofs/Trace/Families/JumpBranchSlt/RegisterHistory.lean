import Airbender.Proofs.Trace.Families.JumpBranchSlt.PortReads

namespace Airbender.JumpBranchSlt.Proofs
open Trace Reference.RiscV.Sail Reference.Sail

/-- Derived clock order and actual public decoding identify each original Sail
    register access in its real native history segment. No segment state is supplied. -/
theorem image_register_history {trace : Data mersenne31Modulus JumpBranchSltFamily}
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
            .ok () rowAfter := by
  obtain ⟨history, rows, after, consistent, permutation, ordered, sail, final⟩ :=
    image_row_history (by decide) inputs accepted decoded aligned
  refine ⟨history, rows, after, consistent, permutation, ordered, sail, final, ?_⟩
  intro newer row older shape
  have present : row ∈ trace.rows := permutation.mem_iff.mp (by rw [shape]; simp)
  obtain ⟨entry, member, source, query⟩ := decoded_sources (by decide) image accepted decoded row present
  have split : SailHistory cells
      ((newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) ++
        ((rowEvents trace.memoryEpoch row).reverse ++
        (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse))) before after := by
    simpa only [shape, List.flatMap_append, List.flatMap_cons, List.append_assoc] using sail
  obtain ⟨rowAfter, past, future⟩ := Trace.Proofs.sail_history_append.mp split
  obtain ⟨rowBefore, earlier, current⟩ := Trace.Proofs.sail_history_append.mp past
  refine ⟨entry, member, rowBefore, rowAfter, source, query, earlier, current, future, ?_⟩
  cases row with
  | mk family w =>
    cases family
    have reads := history_register_reads (by decide) trace.memoryEpoch current query
    exact ⟨reads.1, reads.2,
      history_destination_read (by decide) trace.memoryEpoch current query,
      history_register_write (by decide) trace.memoryEpoch current query⟩

end Airbender.JumpBranchSlt.Proofs
