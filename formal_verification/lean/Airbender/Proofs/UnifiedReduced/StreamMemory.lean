import Airbender.Proofs.UnifiedReduced.StreamDecoder
import Airbender.Proofs.UnifiedReduced.WorkerExecution
import Airbender.Review.Helpers.UnifiedReduced.NativeMemory

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Combined stream decoding supplies one exact machine and worker history.
The round-mask contract stays explicit for the supported-use induction. -/
theorem memory_effects
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program before ca oa cells)
    (rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round) :
    MixedMemoryEffects data before cells := by
  have requests := request_binding (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization requests
  have initialized : Transfer.Inputs (mixedData data) before cells :=
    ⟨inputs.initialization, inputs.distinct⟩
  have zeroRules := Stream.Proofs.mixed_zero_rules_of_program (by decide) (by decide)
    accepted inputs.publicProgram inputs.ordinaryProgram requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) zeroRules
  have rules := mixed_write_rules_of_tables (by decide) (by decide)
    accepted inputs.tables rounds
  have words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded := by
    intro edge present
    exact ⟨Transfer.read_bounds facts initialized rules edge present,
      Transfer.produced_bounds facts initialized rules edge.2
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩)))⟩
  have zero : ∀ edge ∈ (mixedData data).steps,
      edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    intro edge present same
    have value := zeroRules edge present same (by
      intro previous member _ key
      exact zeroReads previous member key)
    rw [value]
    rfl
  obtain ⟨history, events, after, bound, permutation, order, realized, final⟩ :=
    Transfer.native_sail_history facts initialized inputs.aligned zero
  refine ⟨requests, zeroReads, words, Transfer.terminal_bounds facts initialized rules, ?_, ?_, ?_⟩
  · intro edge present
    obtain ⟨cell, member, same⟩ :=
      Transfer.initialized_cell facts initialized.toBoundaryInputs present
    exact ⟨cell, member, same, cell_address_bound cell⟩
  · apply Delegation.Caller.Proofs.worker_effects_of_reads
      accepted.workerConstraints inputs.tables rounds accepted.workerActive
    intro row member port present
    exact (words _ (mixed_worker_member member present)).1
  · have workers := all_worker_execution (by decide) (by decide) accepted
      inputs.publicProgram inputs.initialization inputs.distinct inputs.aligned
      permutation order realized
    exact ⟨events, after, permutation, order, realized,
      fun worker member _ => (workers worker member).1,
      mixed_cycle_execution (by decide) (by decide) accepted.toRequestChecks
        inputs.publicProgram requests permutation order realized,
      Transfer.terminal_sail_reads facts initialized bound final⟩

end Airbender.UnifiedReduced.Caller.Stream.Proofs
