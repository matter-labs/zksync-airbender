import Human.Trace.Delegation.RVSharedSpans
import Slop.Delegation.RVSharedMemory
import Slop.Delegation.WorkerProjection
import Slop.Final.Trace.Workers.Blake2G.RVTheorems
import Slop.Final.Trace.Workers.Blake2Round.RVTheorems
import Slop.Final.Trace.Workers.Keccak.RVTheorems

/-! RV siblings of the worker-projection and shared-span proofs (`WorkerProjection.lean`, `SpanBinding.lean`,
    `SharedSpans.lean`): the projected worker pool is initialized from the shared `initialImageRV` seeds, and the RV
    worker span theorems (`rv_workvector_soundness`, `rv_compression_soundness`, `rv_permutation_soundness`) give the
    reference result together with the delegate link. -/

namespace Airbender.Delegation.Caller.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

private theorem rv_caller_addresses [Fact p.Prime] {data : RVRequestTrace p}
    {before : RV.State} (accepted : RVSharedMemoryAccepted data)
    (requests : RVRequestBinding data before) :
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

private theorem rv_filtered_shared_tokens [Fact p.Prime] {data : RVRequestTrace p}
    {before : RV.State} (accepted : RVSharedMemoryAccepted data)
    (requests : RVRequestBinding data before) (written : Bool) :
    ((data.sharedSteps.map fun edge => if written then edge.2 else edge.1).filter fun token =>
      token.address != (Cell.register 0).addressCode) =
    data.workers.steps.map (fun edge => if written then edge.2 else edge.1) :=
  filtered_architectural_tokens _ _ (rv_caller_addresses accepted requests) worker_addresses written

theorem rv_worker_projection_accepted [Fact p.Prime] {data : RVRequestTrace p}
    {before : RV.State} (accepted : RVSharedMemoryAccepted data)
    (requests : RVRequestBinding data before) : MemoryAccepted data.workerProjection := by
  refine ⟨accepted.workerConstraints, ?_⟩
  have matching := accepted.memory.filter fun token =>
    token.address != (Cell.register 0).addressCode
  have writes := rv_filtered_shared_tokens accepted requests true
  have reads := rv_filtered_shared_tokens accepted requests false
  change (data.sharedSteps.map Prod.snd).filter _ = data.workers.steps.map Prod.snd at writes
  change (data.sharedSteps.map Prod.fst).filter _ = data.workers.steps.map Prod.fst at reads
  simp only [List.filter_append, writes, reads] at matching
  exact matching

theorem rv_worker_projection_inputs [Fact p.Prime] {data : RVRequestTrace p}
    {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (inputs : RVSharedMemoryInputs data before addresses cells)
    (requests : RVRequestBinding data before) :
    RVMemoryInputs data.workerProjection before (workerCells cells) := by
  refine ⟨Transfer.rv_image_restriction inputs.initialization
    (fun address => address != (Cell.register 0).addressCode), ?_, requests.clockRoom,
    fun row member => (requests.clocks row member).2⟩
  exact inputs.distinct.sublist (List.filter_sublist.map Cell.addressCode)

theorem rv_span_keccak_control_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {workers : MemoryData p} {before : RV.State} {cells : List Cell}
    (accepted : MemoryAccepted workers) (inputs : RVMemoryInputs workers before cells)
    (protocol : HashSpan.RVProtocol workers before .keccak) : Cell.register 10 ∈ cells := by
  have nonempty : workers.rows ≠ [] := by
    intro empty
    have count := protocol.calls
    rw [empty] at count
    simp [HashSpan.callCount] at count
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil workers.rows nonempty
  have family : row.family = .keccak := protocol.family row member
  have port : Keccak.importedConstraintsMemoryPorts[0] ∈ row.ports.toList := by
    simp [Row.ports, family, Keccak.importedConstraintsMemoryPorts]
  have edge : (readToken row.assignment Keccak.importedConstraintsMemoryPorts[0],
      row.writeToken Keccak.importedConstraintsMemoryPorts[0]) ∈ workers.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨_, port, rfl⟩⟩
  have seed := inputs.toRVBoundaryInputs.toSeed
  obtain ⟨cell, present, same⟩ := SeedTransfer.initialized_cell
    (Delegation.SeedProofs.transfer_facts hp accepted seed) seed.toSeedInputs edge
  have code : cell.addressCode = (Cell.register 10).addressCode := by
    simpa [readToken, Keccak.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] using same
  have equal := cell_address_injective code
  exact equal ▸ present

theorem rv_hash_span_binding [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : MemoryData p} {before : RV.State} {cells : List Cell} {span : HashSpan}
    (accepted : MemoryAccepted workers) (inputs : RVMemoryInputs workers before cells)
    (protocol : HashSpan.RVProtocol workers before span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ after, span.RVResult workers before after cells := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have byteInverse : 256 * (-7864320 : ZMod p) = 1 := by linear_combination clockInverse
  cases span with
  | blakeG reduced =>
    have abi : Blake2G.RVCallInputs workers before cells reduced := by
      refine ⟨inputs, protocol.tables, protocol.family, ?_, protocol.controlStart, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      have execution := active row member
      simpa [Row.columns, HashSpan.family, family, Blake2G.importedConstraintsDelegationColumns,
        Blake2G.Variables.execute] using execution
    exact Blake2G.Native.rv_workvector_soundness (by omega) rotationInverse accepted abi aligned
  | blakeRound flags =>
    have abi : Blake2Round.RVCallInputs workers before cells flags :=
      ⟨inputs, protocol.tables, protocol.family, protocol.controlStart, protocol.calls⟩
    exact Blake2Round.Native.rv_compression_soundness (by omega) rotationInverse accepted abi aligned
  | keccak =>
    have abi : Keccak.RVCallInputs workers before cells := by
      refine ⟨inputs, rv_span_keccak_control_cell (by norm_num [timestampBase]; omega) accepted inputs protocol,
        protocol.controlStart, protocol.family, ?_, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      have execution := active row member
      simpa [Row.columns, HashSpan.family, family, Keccak.importedConstraintsDelegationColumns,
        Keccak.Variables.execute] using execution
    exact Keccak.Native.rv_permutation_soundness hp byteInverse accepted abi protocol.tables aligned

theorem rv_hash_span_result_mapping [Fact p.Prime]
    {workers : MemoryData p} {before after : RV.State} {cells : List Cell} {span : HashSpan}
    (result : span.RVResult workers before after cells) : Delegation.RVTraceMapping workers before after cells := by
  cases span with
  | blakeG _ | blakeRound _ =>
    obtain ⟨_, _, _, _, _, _, trace, _⟩ := result
    exact trace
  | keccak =>
    obtain ⟨_, _, _, _, trace, _⟩ := result
    exact trace

theorem rv_projected_shared_terminal [Fact p.Prime] {data : RVRequestTrace p}
    {before after : RV.State} {cells : List Cell}
    (mapping : Delegation.RVTraceMapping data.workerProjection before after (workerCells cells))
    (registers : ∀ token ∈ data.machine.terminalMemory, token.address = (Cell.register 0).addressCode →
      Cell.register 0 ∈ cells ∧ token.word.toBitVec = 0) :
    RVSharedTerminalState data after cells := by
  intro token member
  by_cases zero : token.address = (Cell.register 0).addressCode
  · obtain ⟨present, value⟩ := registers token member zero
    refine ⟨.register 0, present, zero.symm, ?_⟩
    rw [value]
    rfl
  · have projected : token ∈ data.workerProjection.terminal := by
      apply List.mem_filter.mpr
      exact ⟨member, bne_iff_ne.mpr zero⟩
    obtain ⟨cell, present, same, read⟩ := mapping.finalCells token projected
    exact ⟨cell, List.mem_of_mem_filter present, same, read⟩

theorem rv_shared_span_effects [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : HashSpan} (accepted : RVSharedMemoryAccepted data)
    (inputs : RVSharedSpanInputs data before addresses cells span) :
    RVSharedSpanEffects data before cells span := by
  have pcInverse : (-30720 : ZMod p) * 65536 = 1 := by linear_combination clockInverse
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := rv_shared_memory_execution size clockInverse pcInverse accepted inputs.toRVSharedMemoryInputs
  have projected := rv_worker_projection_accepted accepted memory.requests
  have initialized := rv_worker_projection_inputs inputs.toRVSharedMemoryInputs memory.requests
  have aligned : ∀ cell ∈ workerCells cells, cell.Aligned :=
    fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)
  have protocol : HashSpan.RVProtocol data.workerProjection before span :=
    ⟨inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩
  obtain ⟨after, result⟩ := rv_hash_span_binding hp clockInverse projected initialized protocol
    accepted.workerActive aligned
  refine ⟨memory.requests, after, rv_projected_shared_terminal (rv_hash_span_result_mapping result) ?_, result⟩
  intro token member zero
  obtain ⟨_, oldFinal, _, _, _, oldReads⟩ := memory.execution
  obtain ⟨cell, present, same, read⟩ := oldReads token member
  have equal : cell = Cell.register 0 := cell_address_injective (same.trans zero)
  subst cell
  refine ⟨present, ?_⟩
  change some (0 : BitVec 32) = some token.word.toBitVec at read
  exact (Option.some.inj read).symm

end Airbender.Delegation.Caller.Proofs
