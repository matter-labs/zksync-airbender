import Airbender.Proofs.Trace.Families.MulDiv.Execution
import Airbender.Proofs.Trace.StatefulComposition

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- Fetch and original stateful decoding are checked in the actual instruction
    pre-state, after native history and PC bookkeeping. Every local interface
    and intermediate state comes from public construction and native matching. -/
theorem image_fetched_step {trace : Data mersenne31Modulus MulDivFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (row : Row mersenne31Modulus MulDivFamily) (present : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    StepWith decoderFields registerClause setup.program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨entry,member,source,query⟩ := decoded_sources (by decide) image accepted decoded row present
  have sourceHere := entry_source_after_native_history source native past
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change row.start.word = Word.ofBitVec entry.pc at canonical
  have pcWord : row.start.word.toBitVec = entry.pc := by rw [canonical,Word.ofBitVec_roundtrip]
  refine ⟨entry,member,Trace.Proofs.entry_source_retired_state_run sourceHere _,?_,?_⟩
  · simpa only [pcWord] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  · have chosen : registerClause entry.instruction =
        some (clause entry.data.family entry.data.rs1 entry.data.rs2 entry.data.rd) := by
      rw [decoder_instruction source.fields]
      cases entry.data.family <;> rfl
    refine ⟨_,chosen,?_⟩
    have nativeRow := accepted.constraints row present
    have ranges := (image_value_bounds image inputs accepted decoded).1 row present
    have found := decoded row present
    rw [row_decoder_query] at found query
    cases row with
    | mk family w =>
      cases family
      have pcInputs := decoded_inputs (by decide) image nativeRow found
      have bound := ranges importedConstraintsMemoryPorts[0] (by
        change _ ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
      rw [Trace.Proofs.read_word] at bound
      exact local_row_execution nativeRow source.fields query bound pcInputs.2.1 trace.memoryEpoch history

/-- Accepted state matching derives the actual terminal PC range from a native
    successor or the public initial PC, including an empty execution. -/
theorem image_terminal_pc_bound {trace : Data mersenne31Modulus MulDivFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : initialState initial (4,0) = some trace.initial) (accepted : Accepted trace) (decoded : Decoded trace setup) :
    trace.terminal.word.Bounded := by
  have matched := accepted.states.mem_iff.mpr (List.mem_cons_self (l := trace.rows.map Row.start))
  rcases List.mem_cons.mp matched with same | finished
  · rw [same]
    exact Trace.Proofs.initial_pc_bound (by decide) inputs
  · obtain ⟨row,present,same⟩ := List.mem_map.mp finished
    rw [← same]
    have native := accepted.constraints row present
    have found := decoded row present
    rw [row_decoder_query] at found
    cases row with
    | mk family w =>
      cases family
      have pcInputs := decoded_inputs (by decide) image native found
      exact (native_pc_successor (by decide) native
        (initial := ⟨(w 0).val,(w 1).val⟩) (final := ⟨(w 13).val,(w 14).val⟩)
        ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,rfl,rfl⟩ pcInputs.1 pcInputs.2.1).1

/-- Original fetch/decoding/preparation/retirement compose along the native PC
    chain. Real matching constructs every state and actual terminal GPR read;
    original stateful decoder replay is proved instead of supplied. -/
theorem image_execution_soundness {trace : Data mersenne31Modulus MulDivFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (StepWith decoderFields registerClause setup.program) trace initial cells := by
  have clocks := Trace.Proofs.image_clock_boundary (by decide) inputs
  obtain ⟨history,rows,nativeAfter,consistent,permutation,ordered,nativeHistory,matched⟩ :=
    image_row_history (by decide) inputs accepted decoded aligned
  have chain := Trace.Proofs.ordered_row_boundaries (by decide) accepted clocks permutation ordered
  have events : (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [Trace.Proofs.native_events_projection (by decide) accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have pc := Trace.Proofs.initial_state_pc (by decide) inputs.initial
  have step := fun row present {before after events} native past current =>
    image_fetched_step image inputs accepted decoded row present
      (before := before) (after := after) (events := events) native past current
  have execution := Trace.Proofs.compose_native_rows_run pc step rows trace.terminal
    (fun row member => permutation.mem_iff.mp member)
    (fun event member => events.mem_iff.mp member) chain nativeHistory
  exact Trace.Proofs.native_trace_postconditions (by decide) accepted clocks inputs.image inputs.domain pc
    consistent chain nativeHistory matched execution

end Airbender.MulDiv.Proofs
