import Airbender.Proofs.UnifiedReduced.SharedSpans
import Airbender.Proofs.Trace.TransferSplit
import Airbender.Proofs.Delegation.SpanSegments

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

private theorem shared_span_facts [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : Delegation.Caller.HashSpan} (accepted : MixedMemoryAccepted data [])
    (inputs : SharedSpanInputs data before addresses cells span) :
    Transfer.Facts (mixedData data) ∧
      ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode →
        memoryWord edge.2.value = 0 := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.toRequestInputs
  have facts := mixed_memory_facts size clockInverse accepted inputs.toRequestInputs inputs.initialization requests
  have closed := caller_only_zero_closed accepted requests
  have reads := Transfer.read_cell_values facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) closed
  have zero : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0 := by
    intro edge member same
    have value := closed edge member same (reads edge member same)
    rw [value]
    rfl
  exact ⟨facts, zero⟩

theorem shared_span_cut [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : Delegation.Caller.HashSpan} (accepted : MixedMemoryAccepted data [])
    (inputs : SharedSpanInputs data before addresses cells span) (cutoff : Nat) :
    ∃ (middle : List (MemoryToken p)) (events : List MemoryAccess) (after : State),
      Transfer.Facts ⟨data.machine.initialMemory, middle, Transfer.beforeSteps (mixedData data) cutoff⟩ ∧
      Transfer.Facts ⟨middle, data.machine.terminalMemory, Transfer.afterSteps (mixedData data) cutoff⟩ ∧
      events.Perm ((Transfer.beforeSteps (mixedData data) cutoff).map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      SailHistory cells events before after ∧
      ∀ token ∈ middle, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after := by
  obtain ⟨facts, zero⟩ := shared_span_facts hp clockInverse accepted inputs
  exact Transfer.split_sail_state facts ⟨inputs.initialization, inputs.distinct⟩ inputs.aligned zero cutoff

theorem shared_span_execution_cut [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : Delegation.Caller.HashSpan} (accepted : MixedMemoryAccepted data [])
    (inputs : SharedSpanInputs data before addresses cells span) (cutoff : Nat) :
    ∃ (middle : List (MemoryToken p)) (earlierEvents laterEvents : List MemoryAccess) (atCut after : State),
      Transfer.Facts ⟨data.machine.initialMemory, middle, Transfer.beforeSteps (mixedData data) cutoff⟩ ∧
      Transfer.Facts ⟨middle, data.machine.terminalMemory, Transfer.afterSteps (mixedData data) cutoff⟩ ∧
      earlierEvents.Perm ((Transfer.beforeSteps (mixedData data) cutoff).map transferEvent) ∧
      laterEvents.Perm ((Transfer.afterSteps (mixedData data) cutoff).map transferEvent) ∧
      earlierEvents.Pairwise (fun a b => b.1 ≤ a.1) ∧ laterEvents.Pairwise (fun a b => b.1 ≤ a.1) ∧
      SailHistory cells earlierEvents before atCut ∧ SailHistory cells laterEvents atCut after ∧
      SailHistory cells (laterEvents ++ earlierEvents) before after ∧
      (∀ token ∈ middle, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read atCut = .ok (memoryWord token.value) atCut) ∧
      (∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.read after = .ok (memoryWord token.value) after) := by
  obtain ⟨facts, zero⟩ := shared_span_facts hp clockInverse accepted inputs
  exact Transfer.split_sail_execution facts ⟨inputs.initialization, inputs.distinct⟩ inputs.aligned zero cutoff

theorem shared_span_worker_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : Delegation.Caller.HashSpan} (accepted : MixedMemoryAccepted data [])
    (inputs : SharedSpanInputs data before addresses cells span) (lower upper : Nat) :
    Delegation.Proofs.NativeWindow data.workerProjection before
      (Delegation.Caller.workerCells cells) lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.toRequestInputs
  have projected := worker_projection_accepted accepted requests
  have initialized := worker_projection_inputs inputs.initialization inputs.distinct requests
  have aligned : ∀ cell ∈ Delegation.Caller.workerCells cells, cell.Aligned :=
    fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)
  have protocol : Delegation.Caller.HashSpan.Protocol data.workerProjection before span :=
    ⟨inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩
  exact Delegation.Caller.Proofs.hash_span_native_window hp clockInverse projected initialized protocol
    accepted.workerActive aligned lower upper

end Airbender.UnifiedReduced.Caller.Proofs
