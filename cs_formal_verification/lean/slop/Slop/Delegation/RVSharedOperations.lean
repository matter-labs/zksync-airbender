import Human.Trace.Delegation.RVSharedMemory
import Human.Trace.Delegation.RVRequestEffects
import Slop.Delegation.RVSharedMemory
import Slop.Delegation.SharedOperations

/-! RV siblings of the shared word-bound and operation proofs (`SharedBounds.lean`, `SharedOperations.lean`) and of
    `request_operation_effects` (`RequestEffects.lean`): bounds propagate from the `initialImageRV` seeds
    (`rv_image_bounds`); worker effects are the state-free `worker_effects_of_reads`. -/

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- Seed bounds and write rules bound every read, write and terminal word of a transfer. -/
theorem rv_transfer_bounds {data : Transfer.Data p} (facts : Transfer.Facts data)
    (seeds : ∀ token ∈ data.initial, token.word.Bounded) (rules : Transfer.WriteRules data) :
    (∀ edge ∈ data.steps, edge.1.word.Bounded ∧ edge.2.word.Bounded) ∧
      ∀ token ∈ data.terminal, token.word.Bounded := by
  have produced := Transfer.produced_bounds_of_seed facts seeds rules
  refine ⟨fun edge present => ⟨produced _ (facts.matching.mem_iff.mpr
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩)))),
    produced _ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩)))⟩, ?_⟩
  intro token present
  exact produced _ (facts.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl present)))

private theorem rv_worker_rules [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedOperationInputs data before addresses cells) :
    Delegation.Proofs.WriteBoundsFromReads data.workers := by
  apply Delegation.Proofs.operation_rules_of_queries hp inverse accepted.workerConstraints inputs.tables inputs.rounds
  intro row member family
  have active := accepted.workerActive row member
  rw [Delegation.Row.columns, family] at active
  change row.assignment 0 = 1 at active ⊢
  exact active

theorem rv_shared_write_rules [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedOperationInputs data before addresses cells)
    (requests : RVRequestBinding data before) : Transfer.WriteRules (rvSharedData data) := by
  intro edge edgeMember reads
  rcases List.mem_append.mp edgeMember with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ rowMember
    have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
        port = AddSub.importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using portMember
    rcases modes with rfl | rfl
    · exact reads _ edgeMember (Nat.le_refl _)
    · have zero := (requests.callers row caller).1.zeroDestination
      change (destination row.assignment).Bounded
      rw [zero]
      norm_num [Word.Bounded, limbBase]
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    apply rv_worker_rules hp inverse accepted inputs row rowMember ?_ port (by simpa using portMember)
    intro source sourceMember
    have included : (readToken row.assignment source, row.writeToken source) ∈ (rvSharedData data).steps :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, rowMember,
        List.mem_map.mpr ⟨source, by simpa using sourceMember, rfl⟩⟩))
    apply reads _ included
    have same : (row.writeToken source).time = (row.writeToken port).time := by
      simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset row sourceMember,
        Delegation.Proofs.port_offset row (by simpa using portMember)]
    rw [same]

theorem rv_shared_word_bounds [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedOperationInputs data before addresses cells)
    (requests : RVRequestBinding data before) : RVSharedWordBounds data := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have facts := rv_shared_memory_facts size clockInverse accepted inputs.toRVSharedMemoryInputs requests
  have rules := rv_shared_write_rules hp rotationInverse accepted inputs requests
  have bounds := rv_transfer_bounds facts (RVValues.rv_image_bounds inputs.initialization) rules
  exact ⟨bounds.1, bounds.2⟩

theorem rv_shared_operation_effects
    {data : RVRequestTrace babyBearModulus} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVSharedMemoryAccepted data) (inputs : RVSharedOperationInputs data before addresses cells) :
    RVSharedOperationEffects data before cells := by
  have memory := rv_shared_memory_execution (by decide) (by decide) (by decide)
    accepted inputs.toRVSharedMemoryInputs
  have words := rv_shared_word_bounds (by decide) (by decide) (by decide) accepted inputs memory.requests
  refine ⟨memory, words, worker_effects_of_reads accepted.workerConstraints inputs.tables inputs.rounds
    accepted.workerActive ?_⟩
  intro row member port present
  have included : (readToken row.assignment port, row.writeToken port) ∈ data.sharedSteps :=
    List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, member,
      List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩))
  exact (words.accesses _ included).1

theorem rv_request_operation_effects
    {data : RVRequestTrace babyBearModulus} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVRequestAccepted data) (inputs : RVRequestOperationInputs data before addresses cells) :
    RVRequestOperationEffects data before cells := by
  have execution := rv_request_memory_execution (by decide) (by decide) (by decide)
    accepted inputs.publicState
  have initialized := rv_request_worker_inputs execution.requests inputs.publicState.initialization
    inputs.publicState.distinct
  have operation : RVOperationInputs data.workers before cells Keccak.Controller.rows := {
    publicState := initialized
    tables := inputs.tables
    rounds := inputs.rounds
    keccakActive := by
      intro row present family
      have active := accepted.workerActive row present
      rw [Delegation.Row.columns, family] at active
      change row.assignment 0 = 1 at active ⊢
      exact active }
  have words := Delegation.rv_operation_memory_soundness (by decide) (by decide) accepted.workers operation
  exact ⟨execution, words.2, worker_effects_of_reads accepted.workerConstraints inputs.tables inputs.rounds
    accepted.workerActive words.2.reads⟩

end Airbender.Delegation.Caller.Proofs
