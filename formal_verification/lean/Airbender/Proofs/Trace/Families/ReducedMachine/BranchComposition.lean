import Airbender.Proofs.ReducedMachine.NativeBranchExecution
import Airbender.Proofs.Trace.Families.ReducedMachine.BranchCodeHistory
import Airbender.Proofs.Trace.Families.ReducedMachine.BranchResults
import Airbender.Proofs.Trace.Families.ReducedMachine.BranchValues
import Airbender.Proofs.Trace.StatefulComposition

namespace Airbender.ReducedMachine.NativeBranchExecutionProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Fetch and original stateful decoding are checked in the actual instruction
    pre-state, after native history and PC bookkeeping. Every local interface
    and intermediate state comes from public construction and native matching. -/
theorem image_fetched_step {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace)) (decoded : BranchDecodedTrace (fixedData trace) setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ (fixedData trace).nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents (fixedData trace).memoryEpoch row).reverse before after) :
    StepWith branchDecoderFields registerClause setup.program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨entry,member,source,query,_⟩ := NativeBranchDecoderProofs.trace_decoding image accepted decoded row present
  have sourceHere := NativeBranchRegisterProofs.entry_source_after_native_history image accepted decoded source native past
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change row.start.word = Word.ofBitVec entry.pc at canonical
  have pcWord : row.start.word.toBitVec = entry.pc := by rw [canonical,Word.ofBitVec_roundtrip]
  refine ⟨entry,member,Trace.Proofs.entry_source_retired_state_run sourceHere _,?_,?_⟩
  · simpa only [pcWord] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  · have nativeRow := accepted.constraints row present
    have ranges := (NativeBranchRangeProofs.image_value_bounds image inputs accepted decoded).1 row present
    have found := decoded row present
    rw [NativeShiftDecoderProofs.row_query] at found query
    cases row with
    | mk family w =>
      cases family
      have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
      change initialPCWord w = Word.ofBitVec entry.pc at canonical
      have aligned : (initialPCWord w).lo % 4 = 0 := by
        rw [canonical]
        exact (Trace.Proofs.run_sparse_setup_sources image member).2
      have offset := NativeBranchDecoderProofs.immediate_word source.fields query
      have even : (branchOffsetWord w).lo % 2 = 0 := by
        rw [offset]
        exact NativeBranchDecoderProofs.offset_even source
      have readable : ∃ value, before.regs.get? .misa = some value := by
        obtain ⟨value,read⟩ := isa
        exact ⟨value,(Trace.Proofs.sail_history_control_flow_csrs past).1.trans read⟩
      have bound := ranges importedConstraintsMemoryPorts[0] (by
        change _ ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
      have rightBound := ranges importedConstraintsMemoryPorts[1] (by
        change _ ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
      rw [Trace.Proofs.read_word] at bound rightBound
      exact NativeBranchExecutionProofs.local_row_execution nativeRow source.fields query bound rightBound aligned even (fixedData trace).memoryEpoch history readable

/-- Accepted state matching derives the actual terminal PC range from a native
    successor or the public initial PC, including an empty execution. -/
theorem image_terminal_pc_bound {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : BranchDecodedTrace (fixedData trace) setup) : (fixedData trace).terminal.word.Bounded := by
  have matched := accepted.states.mem_iff.mpr (List.mem_cons_self (l := (fixedData trace).rows.map Row.start))
  rcases List.mem_cons.mp matched with same | finished
  · rw [same]
    exact Trace.Proofs.initial_pc_bound (by decide) inputs.initial
  · obtain ⟨row,present,same⟩ := List.mem_map.mp finished
    rw [← same]
    obtain ⟨_,_,_,_,_,effects⟩ := NativeBranchRangeProofs.image_branch_results image inputs accepted decoded row present
    exact effects.2.2.2.2.1


/-- Original fetch/decoding/preparation/retirement compose along the native PC
    chain. Real matching constructs every state and actual terminal GPR read;
    original stateful decoder replay is proved instead of supplied. -/
theorem image_execution_soundness {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace)) (decoded : BranchDecodedTrace (fixedData trace) setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (StepWith branchDecoderFields registerClause setup.program) (fixedData trace) initial cells := by
  have clocks := Trace.Proofs.image_clock_boundary (by decide) inputs
  obtain ⟨history,rows,nativeAfter,consistent,permutation,ordered,nativeHistory,matched⟩ :=
    NativeBranchRegisterProofs.image_row_history image inputs accepted decoded aligned
  have chain := Trace.Proofs.ordered_row_boundaries (by decide) accepted clocks permutation ordered
  have events : (rows.flatMap fun row => (rowEvents (fixedData trace).memoryEpoch row).reverse).Perm (fixedData trace).nativeEvents := by
    rw [Trace.Proofs.native_events_projection (by decide) accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have pc := Trace.Proofs.initial_state_pc (by decide) inputs.initial
  have step := fun row present {before after events} native past current =>
    image_fetched_step image inputs accepted decoded isa row present
      (before := before) (after := after) (events := events) native past current
  have execution := Trace.Proofs.compose_native_rows_run pc step rows (fixedData trace).terminal
    (fun row member => permutation.mem_iff.mp member)
    (fun event member => events.mem_iff.mp member) chain nativeHistory
  exact Trace.Proofs.native_trace_postconditions (by decide) accepted clocks inputs.image inputs.domain pc
    consistent chain nativeHistory matched execution

end Airbender.ReducedMachine.NativeBranchExecutionProofs
