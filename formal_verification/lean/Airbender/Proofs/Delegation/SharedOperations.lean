import Airbender.Proofs.Delegation.SharedBounds
import Airbender.Proofs.Bigint.NativeExecution
import Airbender.Proofs.Blake2G.NativeExecution
import Airbender.Proofs.Blake2Round.NativeExecution
import Airbender.Proofs.Keccak.NativeExecution

namespace Airbender.Delegation.Caller.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true


theorem shared_operation_effects
    {data : RequestTrace babyBearModulus} {before : State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedOperationInputs data before addresses cells) :
    SharedOperationEffects data before cells := by
  have memory := shared_memory_execution (by decide) (by decide) (by decide)
    accepted inputs.toSharedMemoryInputs
  have words := shared_word_bounds (by decide) (by decide) (by decide) accepted inputs memory.requests
  refine ⟨memory, words, ?_⟩
  intro row member
  have holds := accepted.workerConstraints row member
  have reads : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
    intro port present
    have included : (readToken row.assignment port, row.writeToken port) ∈ data.sharedSteps :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, member,
        List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))
    exact (words.accesses _ included).1
  cases row with
  | mk family w =>
    cases family
    all_goals simp only [WorkerEffect, Delegation.Row.constraints, inputs.tables, modeledSetup] at holds ⊢
    all_goals have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    · exact Bigint.Native.Proofs.arithmetic_effects core
    · exact Blake2G.Native.Proofs.native_effects (by decide) (by decide) core reads
    · obtain ⟨round, mask⟩ := inputs.rounds ⟨.blakeRound, w⟩ member rfl
      exact ⟨round, mask, Blake2Round.Native.Proofs.native_effects (by decide) (by decide) round core mask reads⟩
    · have active := accepted.workerActive ⟨.keccak, w⟩ member
      exact Keccak.Native.Proofs.native_effects (by decide) (by decide) core active reads

end Airbender.Delegation.Caller.Proofs
