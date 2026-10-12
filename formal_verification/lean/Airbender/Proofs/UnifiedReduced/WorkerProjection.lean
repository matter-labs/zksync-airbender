import Airbender.Review.UnifiedReduced.WorkerProjection
import Airbender.Proofs.UnifiedReduced.MixedMemoryClocks
import Airbender.Proofs.Delegation.WorkerProjection

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem callers_of_empty_registry [Fact p.Prime] {data : RequestTrace p}
    (accepted : MixedMemoryAccepted data []) : data.callers = data.machine.rows := by
  apply List.filter_eq_self.mpr
  intro row member
  have caller : row ∈ data.callers := by
    by_contra ordinary
    have impossible := accepted.ordinaryDecoded row member ordinary
    change ∃ i : Fin 0, _ at impossible
    obtain ⟨i, _⟩ := impossible
    exact Fin.elim0 i
  exact (List.mem_filter.mp caller).2

theorem caller_only_addresses [Fact p.Prime] {data : RequestTrace p}
    {before : State} (accepted : MixedMemoryAccepted data [])
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.machine.rows.flatMap (fun row => (machinePorts row).toList.map fun port =>
      (readToken row.assignment port, writeToken row.columns row.assignment port)),
      edge.1.address = (Cell.register 0).addressCode ∧ edge.2.address = (Cell.register 0).addressCode := by
  intro edge present
  obtain ⟨row, member, step⟩ := List.mem_flatMap.mp present
  have caller : row ∈ data.callers := (callers_of_empty_registry accepted).symm ▸ member
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  have ports := machine_ports_caller caller
  rw [ports] at portMember
  have modes : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
    simpa [architecturalPorts] using portMember
  rcases modes with rfl | rfl
  · exact ⟨(requests.callers row caller).registers.1, (requests.callers row caller).registers.1⟩
  · exact ⟨(requests.callers row caller).registers.2.1, (requests.callers row caller).registers.2.1⟩

theorem filtered_caller_only_tokens [Fact p.Prime] {data : RequestTrace p}
    {before : State} (accepted : MixedMemoryAccepted data [])
    (requests : RequestBinding data before) (written : Bool) :
    ((data.mixedSteps.map fun edge => if written then edge.2 else edge.1).filter fun token =>
      token.address != (Cell.register 0).addressCode) =
    data.workers.steps.map (fun edge => if written then edge.2 else edge.1) :=
  Delegation.Caller.Proofs.filtered_architectural_tokens _ _
    (caller_only_addresses accepted requests) Delegation.Caller.Proofs.worker_addresses written

theorem worker_projection_accepted [Fact p.Prime] {data : RequestTrace p}
    {before : State} (accepted : MixedMemoryAccepted data [])
    (requests : RequestBinding data before) : Delegation.MemoryAccepted data.workerProjection := by
  refine ⟨accepted.workerConstraints, ?_⟩
  have matching := accepted.memory.filter fun token => token.address != (Cell.register 0).addressCode
  have writes := filtered_caller_only_tokens accepted requests true
  have reads := filtered_caller_only_tokens accepted requests false
  change (data.mixedSteps.map Prod.snd).filter _ = data.workers.steps.map Prod.snd at writes
  change (data.mixedSteps.map Prod.fst).filter _ = data.workers.steps.map Prod.fst at reads
  simp only [List.filter_append, writes, reads] at matching
  exact matching

theorem worker_projection_inputs [Fact p.Prime] {data : RequestTrace p}
    {before : State} {cells : List Cell}
    (image : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup) (requests : RequestBinding data before) :
    Delegation.MemoryInputs data.workerProjection before (Delegation.Caller.workerCells cells) := by
  refine ⟨image_restriction image (fun address => address != (Cell.register 0).addressCode), ?_, fun row member => (requests.clocks row member).2⟩
  exact distinct.sublist (List.filter_sublist.map Cell.addressCode)

end Airbender.UnifiedReduced.Caller.Proofs
