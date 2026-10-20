import Slop.Delegation.SharedBounds
import Slop.Bigint.NativeExecution
import Slop.Blake2G.NativeExecution
import Slop.Blake2Round.NativeExecution
import Slop.Keccak.NativeExecution

namespace Airbender.Delegation.Caller.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true


theorem worker_effects_of_reads
    {data : MemoryData babyBearModulus}
    (constraints : ∀ row ∈ data.rows, FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) (row.constraints data.setup))
    (tables : data.setup = modeledSetup Keccak.Controller.rows)
    (rounds : ∀ row ∈ data.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round)
    (active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1)
    (reads : ∀ row ∈ data.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) :
    ∀ row ∈ data.rows, WorkerEffect row := by
  intro row member
  have holds := constraints row member
  have bounds := reads row member
  cases row with
  | mk family w =>
    cases family
    all_goals simp only [WorkerEffect, Delegation.Row.constraints, tables, modeledSetup] at holds ⊢
    all_goals have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    · exact Bigint.Native.Proofs.arithmetic_effects core
    · exact Blake2G.Native.Proofs.native_effects (by decide) (by decide) core bounds
    · obtain ⟨round, mask⟩ := rounds ⟨.blakeRound, w⟩ member rfl
      exact ⟨round, mask, Blake2Round.Native.Proofs.native_effects (by decide) (by decide) round core mask bounds⟩
    · exact Keccak.Native.Proofs.native_effects (by decide) (by decide) core (active _ member) bounds

theorem shared_operation_effects
    {data : RequestTrace babyBearModulus} {before : State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedOperationInputs data before addresses cells) :
    SharedOperationEffects data before cells := by
  have memory := shared_memory_execution (by decide) (by decide) (by decide)
    accepted inputs.toSharedMemoryInputs
  have words := shared_word_bounds (by decide) (by decide) (by decide) accepted inputs memory.requests
  refine ⟨memory, words, worker_effects_of_reads accepted.workerConstraints inputs.tables inputs.rounds accepted.workerActive ?_⟩
  intro row member port present
  have included : (readToken row.assignment port, row.writeToken port) ∈ data.sharedSteps :=
    List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, member,
      List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))
  exact (words.accesses _ included).1

end Airbender.Delegation.Caller.Proofs
