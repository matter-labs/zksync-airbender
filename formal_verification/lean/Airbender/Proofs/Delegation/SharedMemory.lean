import Airbender.Proofs.Delegation.SharedClocks
import Airbender.Proofs.Trace.TransferValues
import Airbender.Proofs.Trace.TransferTerminal

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

private theorem initial_zero {data : Transfer.Data p} {before : State} {cells : List Cell}
    (image : initialImage before cells = some data.initial) :
    ∀ token ∈ data.initial, token.address = (Cell.register 0).addressCode → token.value = 0 := by
  intro token present same
  obtain ⟨cell, _, value, read, rfl⟩ := image_sources image token present
  have code : cell.addressCode = (Cell.register 0).addressCode := same
  have equal := cell_address_injective code
  subst cell
  have actual : value = 0 := by
    change EStateM.Result.ok (0 : BitVec 32) before = .ok value before at read
    exact (EStateM.Result.ok.inj read).1.symm
  subst value
  rfl

private theorem shared_zero_closed [Fact p.Prime]
    {data : RequestTrace p} {before : State} (accepted : SharedMemoryAccepted data)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.sharedSteps, edge.1.address = (Cell.register 0).addressCode →
      edge.1.value = 0 → edge.2.value = 0 := by
  intro edge member same old
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ rowMember
    have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
        port = AddSub.importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using portMember
    rcases modes with rfl | rfl
    · exact old
    · have zero := (requests.callers row caller).1.zeroDestination
      have encoded := congrArg (fun word : Word => Nat.pair word.lo word.hi) zero
      change _ = Nat.pair 0 0
      simpa only [destination, MemoryToken.word, Nat.pair_unpair] using encoded
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact False.elim (Delegation.Proofs.port_not_zero row (by simpa using present) same)

theorem shared_source_values [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells)
    (requests : RequestBinding data before) :
    ∀ row ∈ data.callers, (sourceToken row.assignment).value = 0 := by
  have facts := shared_memory_facts hp inverse accepted inputs requests
  have closed := shared_zero_closed accepted requests
  have reads := Transfer.read_cell_values facts (Cell.register 0).addressCode 0
    (initial_zero inputs.initialization) closed
  intro row member
  have step : (sourceToken row.assignment,
      writeToken AddSub.importedConstraintsTraceColumns row.assignment
        AddSub.importedConstraintsMemoryPorts[0]) ∈ data.sharedSteps := by
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_flatMap.mpr
    refine ⟨row, accepted.callerRows ▸ member, ?_⟩
    apply List.mem_map.mpr
    exact ⟨AddSub.importedConstraintsMemoryPorts[0], by simp [architecturalPorts], rfl⟩
  exact reads _ step (requests.callers row member).1.sourceAddress

theorem shared_memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedMemoryInputs data before addresses cells) :
    SharedMemoryEffects data before cells := by
  have requests := request_binding_checks hp clockInverse pcInverse accepted.toRequestChecks inputs.publicProgram
  have facts := shared_memory_facts hp clockInverse accepted inputs requests
  have initialized := sharedInputs inputs
  have zero : ∀ edge ∈ (sharedData data).steps,
      edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    have reads := Transfer.read_cell_values facts (Cell.register 0).addressCode 0
      (initial_zero inputs.initialization) (shared_zero_closed accepted requests)
    intro edge present same
    have value := shared_zero_closed accepted requests edge present same (reads edge present same)
    rw [value]
    rfl
  obtain ⟨history, events, after, bound, permutation, order, realized, final⟩ :=
    Transfer.native_sail_history facts initialized inputs.aligned zero
  refine ⟨requests, shared_source_values hp clockInverse accepted inputs requests, ?_, ?_⟩
  · intro row present port member
    have step : (readToken row.assignment port, row.writeToken port) ∈ (sharedData data).steps :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, present,
        List.mem_map.mpr ⟨port, by simpa using member, rfl⟩⟩))
    obtain ⟨cell, _, same⟩ := Transfer.initialized_cell facts initialized step
    rw [address_word same.symm]
    exact cell_address_bound cell
  · exact ⟨events, after, permutation, order, realized,
      Transfer.terminal_sail_reads facts initialized bound final⟩

end Airbender.Delegation.Caller.Proofs
