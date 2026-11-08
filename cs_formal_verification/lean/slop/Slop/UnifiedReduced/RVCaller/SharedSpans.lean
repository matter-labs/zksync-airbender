module
public import Human.Trace.UnifiedReduced.RVMixedMemory
public import Slop.UnifiedReduced.RVCaller.WorkerProjection
public import Slop.Delegation.RVSharedSpans

@[expose] public section

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_caller_only_zero_closed [Fact p.Prime]
    {data : RVRequestTrace p} {before : RV.State} (accepted : RVMixedMemoryAccepted data [])
    (requests : RVRequestBinding data before) :
    ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode →
      edge.1.value = 0 → edge.2.value = 0 := by
  intro edge member same old
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := (rv_callers_of_empty_registry accepted).symm ▸ rowMember
    rw [rv_machine_ports_caller caller] at portMember
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

theorem rv_projected_shared_terminal [Fact p.Prime] {data : RVRequestTrace p}
    {before after : RV.State} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data []) (requests : RVRequestBinding data before)
    (facts : Transfer.Facts (rv_mixedData data))
    (image : initialImageRV before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    (mapping : Delegation.RVTraceMapping data.workerProjection before after (Delegation.Caller.workerCells cells)) :
    RVSharedTerminalState data after cells := by
  intro token member
  by_cases zero : token.address = (Cell.register 0).addressCode
  · have produced := Transfer.produced_cell_values facts (Cell.register 0).addressCode 0
      (Transfer.rv_initial_zero image) (rv_caller_only_zero_closed accepted requests)
    have value := produced token (facts.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member))) zero
    obtain ⟨source, sourceMember, same, _⟩ := SeedTransfer.terminal_path facts (⟨image, distinct⟩ : Transfer.RVInputs _ _ _).toSeed member
    obtain ⟨cell, present, _, _, sourceEq⟩ := RVZero.rv_image_token_sources image source sourceMember
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

theorem rv_shared_span_effects [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : Delegation.Caller.HashSpan} (accepted : RVMixedMemoryAccepted data [])
    (inputs : RVSharedSpanInputs data before addresses cells span) : RVSharedSpanEffects data before cells span := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := rv_request_binding size clockInverse accepted.toRVRequestChecks inputs.toRVRequestInputs
  have facts := rv_mixed_memory_facts size clockInverse accepted inputs.toRVRequestInputs inputs.initialization requests
  have projected := rv_worker_projection_accepted accepted requests
  have initialized := rv_worker_projection_inputs inputs.initialization inputs.distinct requests
  have aligned : ∀ cell ∈ Delegation.Caller.workerCells cells, cell.Aligned :=
    fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)
  have protocol : Delegation.Caller.HashSpan.RVProtocol data.workerProjection before span :=
    ⟨inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩
  obtain ⟨after, result⟩ := Delegation.Caller.Proofs.rv_hash_span_binding hp clockInverse projected initialized
    protocol accepted.workerActive aligned
  exact ⟨requests, after, rv_projected_shared_terminal accepted requests facts inputs.initialization inputs.distinct
    (Delegation.Caller.Proofs.rv_hash_span_result_mapping result), result⟩

end Airbender.UnifiedReduced.Caller.Proofs
