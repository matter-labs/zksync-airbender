import Airbender.Review.Delegation.SharedSpans
import Airbender.Proofs.Delegation.WorkerProjection
import Airbender.Proofs.Blake2G.WorkVectorBinding
import Airbender.Proofs.Blake2Round.CompressionBinding
import Airbender.Proofs.Keccak.PermutationBinding

namespace Airbender.Delegation.Caller.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem projected_shared_terminal [Fact p.Prime] {data : RequestTrace p}
    {before after : State} {cells : List Cell} (memory : SharedMemoryEffects data before cells)
    (mapping : Delegation.TraceMapping data.workerProjection before after (workerCells cells)) :
    SharedTerminalState data after cells := by
  intro token member
  by_cases zero : token.address = (Cell.register 0).addressCode
  · obtain ⟨events, oldFinal, _, _, _, oldReads⟩ := memory.execution
    obtain ⟨cell, present, same, read⟩ := oldReads token member
    have equal : cell = Cell.register 0 := cell_address_injective (same.trans zero)
    subst cell
    have value : token.word.toBitVec = 0 := by
      change EStateM.Result.ok (0 : BitVec 32) oldFinal = .ok token.word.toBitVec oldFinal at read
      exact (EStateM.Result.ok.inj read).1.symm
    exact ⟨.register 0, present, zero.symm, by rw [value]; rfl⟩
  · have projected : token ∈ data.workerProjection.terminal := by
      apply List.mem_filter.mpr
      exact ⟨member, bne_iff_ne.mpr zero⟩
    obtain ⟨cell, present, same, read⟩ := mapping.finalCells token projected
    exact ⟨cell, List.mem_of_mem_filter present, same, read⟩

private theorem keccak_control_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedSpanInputs data before addresses cells .keccak)
    (requests : RequestBinding data before) : Cell.register 10 ∈ workerCells cells := by
  have nonempty : data.workers.rows ≠ [] := by
    intro empty
    have count := inputs.calls
    rw [empty] at count
    simp [HashSpan.callCount] at count
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil data.workers.rows nonempty
  have family : row.family = .keccak := inputs.family row member
  have port : Keccak.importedConstraintsMemoryPorts[0] ∈ row.ports.toList := by
    simp [Delegation.Row.ports, family, Keccak.importedConstraintsMemoryPorts]
  have edge : (readToken row.assignment Keccak.importedConstraintsMemoryPorts[0],
      row.writeToken Keccak.importedConstraintsMemoryPorts[0]) ∈ (sharedData data).steps :=
    List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨_, port, rfl⟩⟩))
  have facts := shared_memory_facts hp inverse accepted inputs.toSharedMemoryInputs requests
  obtain ⟨cell, present, same⟩ := Transfer.initialized_cell facts (sharedInputs inputs.toSharedMemoryInputs) edge
  have code : cell.addressCode = (Cell.register 10).addressCode := by
    simpa [readToken, Keccak.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] using same
  have equal : cell = Cell.register 10 := cell_address_injective code
  subst cell
  exact List.mem_filter.mpr ⟨present, by decide⟩

theorem shared_span_effects [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : HashSpan} (accepted : SharedMemoryAccepted data)
    (inputs : SharedSpanInputs data before addresses cells span) : SharedSpanEffects data before cells span := by
  have pcInverse : (-30720 : ZMod p) * 65536 = 1 := by linear_combination clockInverse
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have byteInverse : 256 * (-7864320 : ZMod p) = 1 := by linear_combination clockInverse
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := shared_memory_execution size clockInverse pcInverse accepted inputs.toSharedMemoryInputs
  have projected := worker_projection_accepted accepted memory.requests
  have initialized := worker_projection_inputs inputs.toSharedMemoryInputs memory.requests
  have aligned : ∀ cell ∈ workerCells cells, cell.Aligned :=
    fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)
  refine ⟨memory.requests, ?_⟩
  cases span with
  | blakeG reduced =>
    have abi : Blake2G.CallInputs data.workerProjection before (workerCells cells) reduced := by
      refine ⟨initialized, inputs.tables, inputs.family, ?_, inputs.controlStart, inputs.calls⟩
      intro row member
      have family := inputs.family row member
      have active := accepted.workerActive row member
      simpa [Delegation.Row.columns, HashSpan.family, family, Blake2G.importedConstraintsDelegationColumns,
        Blake2G.Variables.execute] using active
    obtain ⟨after, state, message, input, words, output, mapping, trace, result⟩ :=
      Blake2G.Proofs.workvector_binding (by omega) rotationInverse projected abi aligned
    exact ⟨after, projected_shared_terminal memory trace, state, message, input, words, output, mapping, trace, result⟩
  | blakeRound flags =>
    have abi : Blake2Round.CallInputs data.workerProjection before (workerCells cells) flags :=
      ⟨initialized, inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩
    obtain ⟨after, state, pointer, input, message, output, mapping, trace, result⟩ :=
      Blake2Round.Proofs.compression_binding (by omega) rotationInverse projected abi aligned
    exact ⟨after, projected_shared_terminal memory trace, state, pointer, input, message, output, mapping, trace, result⟩
  | keccak =>
    have abi : Keccak.CallInputs data.workerProjection before (workerCells cells) := by
      refine ⟨initialized, keccak_control_cell size clockInverse accepted inputs memory.requests,
        inputs.controlStart, inputs.family, ?_, inputs.calls⟩
      intro row member
      have family := inputs.family row member
      have active := accepted.workerActive row member
      simpa [Delegation.Row.columns, HashSpan.family, family, Keccak.importedConstraintsDelegationColumns,
        Keccak.Variables.execute] using active
    obtain ⟨after, pointer, input, output, mapping, trace, result⟩ :=
      Keccak.Proofs.permutation_binding hp byteInverse projected abi inputs.tables aligned
    exact ⟨after, projected_shared_terminal memory trace, pointer, input, output, mapping, trace, result⟩

end Airbender.Delegation.Caller.Proofs
