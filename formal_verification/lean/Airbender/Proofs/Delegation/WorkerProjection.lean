import Airbender.Review.Helpers.Delegation.WorkerProjection
import Airbender.Proofs.Delegation.SharedMemory
import Airbender.Proofs.Trace.ImageRestriction

namespace Airbender.Delegation.Caller.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

private theorem caller_addresses [Fact p.Prime] {data : RequestTrace p}
    {before : Reference.RiscV.Sail.State} (accepted : SharedMemoryAccepted data)
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.machine.rows.flatMap (fun row => architecturalSteps row.assignment),
      edge.1.address = (Cell.register 0).addressCode ∧
      edge.2.address = (Cell.register 0).addressCode := by
  intro edge member
  obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  have caller : row ∈ data.callers := accepted.callerRows.symm ▸ rowMember
  have binding := (requests.callers row caller).1
  have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
      port = AddSub.importedConstraintsMemoryPorts[2] := by
    simpa [architecturalPorts] using portMember
  rcases modes with rfl | rfl
  · exact ⟨binding.sourceAddress, binding.sourceAddress⟩
  · exact ⟨binding.destinationAddress, binding.destinationAddress⟩

theorem worker_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address ≠ (Cell.register 0).addressCode ∧
      edge.2.address ≠ (Cell.register 0).addressCode := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  have nonzero := Delegation.Proofs.port_not_zero row (by simpa using portMember)
  exact ⟨nonzero, nonzero⟩

theorem filtered_architectural_tokens {p : Nat}
    (machine workers : List (MemoryToken p × MemoryToken p))
    (callerAddresses : ∀ edge ∈ machine, edge.1.address = (Cell.register 0).addressCode ∧
      edge.2.address = (Cell.register 0).addressCode)
    (workerAddresses : ∀ edge ∈ workers, edge.1.address ≠ (Cell.register 0).addressCode ∧
      edge.2.address ≠ (Cell.register 0).addressCode) (written : Bool) :
    (((machine ++ workers).map fun edge => if written then edge.2 else edge.1).filter fun token =>
      token.address != (Cell.register 0).addressCode) =
    workers.map (fun edge => if written then edge.2 else edge.1) := by
  have removed :
      ((machine).map
        (fun edge => if written then edge.2 else edge.1)).filter
        (fun token => token.address != (Cell.register 0).addressCode) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro token member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
    cases written <;> simp [(callerAddresses edge present).1, (callerAddresses edge present).2]
  have kept :
      (workers.map (fun edge => if written then edge.2 else edge.1)).filter
        (fun token => token.address != (Cell.register 0).addressCode) =
      workers.map (fun edge => if written then edge.2 else edge.1) := by
    apply List.filter_eq_self.mpr
    intro token member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
    cases written with
    | false => simpa only [Bool.false_eq_true, if_false, bne_iff_ne] using (workerAddresses edge present).1
    | true => simpa only [ite_true, bne_iff_ne] using (workerAddresses edge present).2
  simp only [List.map_append, List.filter_append, removed, kept, List.nil_append]

private theorem filtered_shared_tokens [Fact p.Prime] {data : RequestTrace p}
    {before : Reference.RiscV.Sail.State} (accepted : SharedMemoryAccepted data)
    (requests : RequestBinding data before) (written : Bool) :
    ((data.sharedSteps.map fun edge => if written then edge.2 else edge.1).filter fun token =>
      token.address != (Cell.register 0).addressCode) =
    data.workers.steps.map (fun edge => if written then edge.2 else edge.1) :=
  filtered_architectural_tokens _ _ (caller_addresses accepted requests) worker_addresses written

theorem worker_projection_accepted [Fact p.Prime] {data : RequestTrace p}
    {before : Reference.RiscV.Sail.State} (accepted : SharedMemoryAccepted data)
    (requests : RequestBinding data before) : MemoryAccepted data.workerProjection := by
  refine ⟨accepted.workerConstraints, ?_⟩
  have matching := accepted.memory.filter fun token =>
    token.address != (Cell.register 0).addressCode
  have writes := filtered_shared_tokens accepted requests true
  have reads := filtered_shared_tokens accepted requests false
  change (data.sharedSteps.map Prod.snd).filter _ = data.workers.steps.map Prod.snd at writes
  change (data.sharedSteps.map Prod.fst).filter _ = data.workers.steps.map Prod.fst at reads
  simp only [List.filter_append, writes, reads] at matching
  exact matching

theorem worker_projection_inputs [Fact p.Prime] {data : RequestTrace p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (inputs : SharedMemoryInputs data before addresses cells)
    (requests : RequestBinding data before) :
    MemoryInputs data.workerProjection before (workerCells cells) := by
  refine ⟨image_restriction inputs.initialization
    (fun address => address != (Cell.register 0).addressCode), ?_, requests.clockRoom,
    fun row member => (requests.clocks row member).2⟩
  exact inputs.distinct.sublist (List.filter_sublist.map Cell.addressCode)

end Airbender.Delegation.Caller.Proofs
