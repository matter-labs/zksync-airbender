import Airbender.Proofs.Trace.Families.JumpBranchSlt.CodeHistory
import Airbender.Proofs.Trace.Families.JumpBranchSlt.JumpExecution
import Airbender.Proofs.Trace.Families.JumpBranchSlt.BranchExecution
import Airbender.Proofs.Trace.Families.JumpBranchSlt.ComparisonExecution

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- Actual native GPR history preserves public bytes and original decoding.
    The exact public constructor dispatches to the checked native retirement;
    row PCs, CSR reads, operands, results and after-states are all derived. -/
theorem image_fetched_step {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : (∃ row ∈ trace.rows, (row.assignment 12).val = 2) →
      initial.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
        initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (row : Row mersenne31Modulus JumpBranchSltFamily) (present : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    StepWith decoderFields registerClause setup.program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨entry,member,source,query⟩ := decoded_sources (by decide) image accepted decoded row present
  have replay := (Trace.Proofs.sparse_setup_sources image member).2.1
  have sourceHere := entry_source_after_native_history source replay native past
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change row.start.word = Word.ofBitVec entry.pc at canonical
  have pcWord : row.start.word.toBitVec = entry.pc := by rw [canonical,Word.ofBitVec_roundtrip]
  refine ⟨entry,member,Trace.Proofs.entry_source_retired_state sourceHere _ replay,?_,?_⟩
  · simpa only [pcWord] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  · have masks := (decoded_mask_flag image accepted decoded row present).1
    cases row with
    | mk family w =>
      cases family
      rw [row_decoder_query] at query
      change ∃ clause, registerClause entry.instruction = some clause ∧
        run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS
            (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec)
      by_cases jump : (w 12).val ∈ [1,2]
      · exact image_jump_retirement image inputs accepted decoded isa
          (fun indirect => configuration ⟨_,present,indirect⟩) present jump source.fields query history past
      by_cases comparison : (w 12).val ∈ [4,8]
      · exact image_comparison_retirement image inputs accepted decoded present comparison source.fields query history
      have branch : (w 12).val = 16 := by
        change (w 12).val ∈ [1,2,4,8,16] at masks
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at masks jump comparison
        omega
      exact image_branch_retirement image inputs accepted decoded isa present branch source.fields query history past

/-- Actual candidate range queries and full state matching bound the external
    terminal PC, including empty traces, with no closure premise. -/
theorem image_terminal_pc_bound {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup) :
    trace.terminal.word.Bounded := by
  have matched := accepted.states.mem_iff.mpr (List.mem_cons_self (l := trace.rows.map Row.start))
  rcases List.mem_cons.mp matched with same | finished
  · rw [same]
    exact Trace.Proofs.initial_pc_bound (by decide) inputs.initial
  · obtain ⟨row,present,same⟩ := List.mem_map.mp finished
    rw [← same]
    have mask := (decoded_mask_flag image accepted decoded row present).1
    have native := accepted.constraints row present
    cases row with
    | mk family w =>
      cases family
      exact pc_bounds native mask

/-- Shared original fetch/decode/retirement composition derives every row state,
    complete PC chain and actual terminal GPR reads from native acceptance and
    public initialization. No terminal bound or per-row step premise is supplied. -/
theorem image_execution_soundness {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : (∃ row ∈ trace.rows, (row.assignment 12).val = 2) →
      initial.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
        initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (StepWith decoderFields registerClause setup.program) trace initial cells := by
  have clocks := Trace.Proofs.image_clock_boundary (by decide) inputs
  have pureDecoders := fun entry member => (Trace.Proofs.sparse_setup_sources image (entry := entry) member).2.1
  obtain ⟨history,rows,nativeAfter,consistent,permutation,ordered,nativeHistory,matched⟩ :=
    image_row_history (by decide) inputs accepted decoded aligned
  have chain := Trace.Proofs.ordered_row_boundaries (by decide) accepted clocks permutation ordered
  have events : (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [Trace.Proofs.native_events_projection (by decide) accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have pc := Trace.Proofs.initial_state_pc (by decide) inputs.initial
  have step := fun row present {before after events} native past current =>
    image_fetched_step image inputs accepted decoded isa configuration row present
      (before := before) (after := after) (events := events) native past current
  have execution := Trace.Proofs.compose_native_rows pc pureDecoders step rows trace.terminal
    (fun row member => permutation.mem_iff.mp member)
    (fun event member => events.mem_iff.mp member) chain nativeHistory
  exact Trace.Proofs.native_trace_postconditions (by decide) accepted clocks inputs.image inputs.domain pc
    consistent chain nativeHistory matched execution

end Airbender.JumpBranchSlt.Proofs
