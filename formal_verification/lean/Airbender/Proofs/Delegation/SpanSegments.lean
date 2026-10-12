import Airbender.Proofs.Delegation.SpanBinding
import Airbender.Proofs.Delegation.Operations
import Airbender.Proofs.Delegation.NativeSegments
import Airbender.Proofs.Delegation.WorkerProjection

namespace Airbender.Delegation.Caller.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem hash_span_write_rules [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : MemoryData p} {before : State} {cells : List Cell} {span : HashSpan}
    (accepted : MemoryAccepted workers) (inputs : MemoryInputs workers before cells)
    (protocol : HashSpan.Protocol workers before span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1) :
    Delegation.Proofs.WriteBoundsFromReads workers := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  apply Delegation.Proofs.operation_rules_of_queries (by omega) rotationInverse
    accepted.constraints protocol.tables
  · intro row member round
    cases span with
    | blakeG reduced =>
      have family := protocol.family row member
      change row.family = .blakeG at family
      exact False.elim (by rw [family] at round; cases round)
    | blakeRound flags =>
      have abi : Blake2Round.CallInputs workers before cells flags :=
        ⟨inputs, protocol.tables, protocol.family, protocol.controlStart, protocol.calls⟩
      exact Blake2Round.Proofs.call_masks (by norm_num [timestampBase]; omega) accepted abi row member
    | keccak =>
      have family := protocol.family row member
      change row.family = .keccak at family
      exact False.elim (by rw [family] at round; cases round)
  · intro row member family
    have execution := active row member
    simpa [Row.columns, family, Keccak.importedConstraintsDelegationColumns,
      Keccak.Variables.execute] using execution

theorem hash_span_native_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : MemoryData p} {before : State} {cells : List Cell} {span : HashSpan}
    (accepted : MemoryAccepted workers) (inputs : MemoryInputs workers before cells)
    (protocol : HashSpan.Protocol workers before span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (lower upper : Nat) :
    Delegation.Proofs.NativeWindow workers before cells lower upper :=
  Delegation.Proofs.native_span_window (by norm_num [timestampBase]; omega) accepted inputs
    (hash_span_write_rules hp clockInverse accepted inputs protocol active) aligned lower upper

theorem shared_span_worker_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : HashSpan} (accepted : SharedMemoryAccepted data)
    (inputs : SharedSpanInputs data before addresses cells span) (lower upper : Nat) :
    Delegation.Proofs.NativeWindow data.workerProjection before (workerCells cells) lower upper := by
  have pcInverse : (-30720 : ZMod p) * 65536 = 1 := by linear_combination clockInverse
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := shared_memory_execution size clockInverse pcInverse accepted inputs.toSharedMemoryInputs
  have projected := worker_projection_accepted accepted memory.requests
  have initialized := worker_projection_inputs inputs.toSharedMemoryInputs memory.requests
  have aligned : ∀ cell ∈ workerCells cells, cell.Aligned :=
    fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)
  have protocol : HashSpan.Protocol data.workerProjection before span :=
    ⟨inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩
  exact hash_span_native_window hp clockInverse projected initialized protocol accepted.workerActive
    aligned lower upper

end Airbender.Delegation.Caller.Proofs
