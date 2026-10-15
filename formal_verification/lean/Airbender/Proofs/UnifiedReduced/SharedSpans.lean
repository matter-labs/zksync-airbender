import Airbender.Review.Trace.UnifiedReduced.SharedSpans
import Airbender.Proofs.UnifiedReduced.WorkerProjection
import Airbender.Proofs.Delegation.SpanBinding

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem caller_only_zero_closed [Fact p.Prime]
    {data : RequestTrace p} {before : State} (accepted : MixedMemoryAccepted data [])
    (requests : RequestBinding data before) :
    ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode →
      edge.1.value = 0 → edge.2.value = 0 := by
  intro edge member same old
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := (callers_of_empty_registry accepted).symm ▸ rowMember
    rw [machine_ports_caller caller] at portMember
    have modes : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using portMember
    rcases modes with rfl | rfl
    · exact old
    · have encoded := congrArg (fun word : Word => Nat.pair word.lo word.hi)
        (requests.callers row caller).registers.2.2
      change _ = Nat.pair 0 0
      have columns : row.columns = importedConstraintsTraceColumns := by cases row.family; rfl
      rw [columns]
      simpa only [destinationToken, MemoryToken.word, Nat.pair_unpair] using encoded
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact False.elim (Delegation.Proofs.port_not_zero row (by simpa using present) same)

theorem projected_shared_terminal [Fact p.Prime] {data : RequestTrace p}
    {before after : State} {cells : List Cell}
    (accepted : MixedMemoryAccepted data []) (requests : RequestBinding data before)
    (facts : Transfer.Facts (mixedData data))
    (image : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    (mapping : Delegation.TraceMapping data.workerProjection before after (Delegation.Caller.workerCells cells)) :
    SharedTerminalState data after cells := by
  intro token member
  by_cases zero : token.address = (Cell.register 0).addressCode
  · have produced := Transfer.produced_cell_values facts (Cell.register 0).addressCode 0
      (Delegation.Caller.Proofs.initial_zero image) (caller_only_zero_closed accepted requests)
    have value := produced token (facts.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member))) zero
    obtain ⟨source, sourceMember, same, _⟩ := Transfer.terminal_path facts (⟨image, distinct⟩ : Transfer.Inputs _ _ _).toBoundaryInputs member
    obtain ⟨cell, present, _, _, sourceEq⟩ := image_sources image source sourceMember
    have code : cell.addressCode = (Cell.register 0).addressCode := by
      rw [sourceEq] at same
      exact same.trans zero
    have equal := cell_address_injective code
    subst cell
    have word : token.word.toBitVec = 0 := by
      simp only [MemoryToken.word, value, Nat.unpair_zero]
      rfl
    exact ⟨.register 0, present, zero.symm, by rw [word]; rfl⟩
  · have projected : token ∈ data.workerProjection.terminal := by
      exact List.mem_filter.mpr ⟨member, bne_iff_ne.mpr zero⟩
    obtain ⟨cell, present, same, read⟩ := mapping.finalCells token projected
    exact ⟨cell, List.mem_of_mem_filter present, same, read⟩

theorem shared_span_effects [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : Delegation.Caller.HashSpan} (accepted : MixedMemoryAccepted data [])
    (inputs : SharedSpanInputs data before addresses cells span) : SharedSpanEffects data before cells span := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.toRequestInputs
  have facts := mixed_memory_facts size clockInverse accepted inputs.toRequestInputs inputs.initialization requests
  have projected := worker_projection_accepted accepted requests
  have initialized := worker_projection_inputs inputs.initialization inputs.distinct requests
  have aligned : ∀ cell ∈ Delegation.Caller.workerCells cells, cell.Aligned :=
    fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)
  have protocol : Delegation.Caller.HashSpan.Protocol data.workerProjection before span :=
    ⟨inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩
  obtain ⟨after, result⟩ := Delegation.Caller.Proofs.hash_span_binding hp clockInverse projected initialized
    protocol accepted.workerActive aligned
  exact ⟨requests, after, projected_shared_terminal accepted requests facts inputs.initialization inputs.distinct
    (Delegation.Caller.Proofs.hash_span_result_mapping result), result⟩

end Airbender.UnifiedReduced.Caller.Proofs
