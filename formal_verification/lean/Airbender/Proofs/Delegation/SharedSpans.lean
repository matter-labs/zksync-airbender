import Airbender.Review.Trace.Delegation.SharedSpans
import Airbender.Proofs.Delegation.WorkerProjection
import Airbender.Proofs.Delegation.SpanBinding

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

theorem shared_span_effects [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : HashSpan} (accepted : SharedMemoryAccepted data)
    (inputs : SharedSpanInputs data before addresses cells span) : SharedSpanEffects data before cells span := by
  have pcInverse : (-30720 : ZMod p) * 65536 = 1 := by linear_combination clockInverse
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := shared_memory_execution size clockInverse pcInverse accepted inputs.toSharedMemoryInputs
  have projected := worker_projection_accepted accepted memory.requests
  have initialized := worker_projection_inputs inputs.toSharedMemoryInputs memory.requests
  have aligned : ∀ cell ∈ workerCells cells, cell.Aligned :=
    fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)
  have protocol : HashSpan.Protocol data.workerProjection before span :=
    ⟨inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩
  obtain ⟨after, result⟩ := hash_span_binding hp clockInverse projected initialized protocol accepted.workerActive aligned
  exact ⟨memory.requests, after, projected_shared_terminal memory (hash_span_result_mapping result), result⟩

end Airbender.Delegation.Caller.Proofs
