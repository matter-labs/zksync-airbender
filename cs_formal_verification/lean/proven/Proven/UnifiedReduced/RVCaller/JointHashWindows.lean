module
public import Human.Trace.UnifiedReduced.RVJointHashWindows
public import Proven.UnifiedReduced.RVCaller.WindowProjection
public import Proven.UnifiedReduced.RVCaller.SpanTarget
public import Proven.Blake2G.RVWindows
public import Proven.Blake2Round.RVWindows
public import Proven.Defs.Trace.Workers.Blake2Round.Call

@[expose] public section

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_round_window_masks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : RVRequestTrace p} {before : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    {flags : Fin 8} {lower upper : Nat} (accepted : RVMixedMemoryAccepted data [])
    (inputs : RVJointHashWindowInputs data before addresses cells (.blakeRound flags) lower upper)
    (requests : RVRequestBinding data before) :
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  have projected := rv_worker_projection_accepted accepted requests
  have initialized := rv_worker_projection_inputs inputs.initialization inputs.distinct requests
  have nonempty : data.workers.windowRows lower upper ≠ [] := by
    intro empty
    have count := inputs.calls
    rw [empty] at count
    change 0 = if flags.val % 2 = 1 then 7 else 10 at count
    split_ifs at count
  have boundary := initialized.toRVBoundaryInputs
  have seed : Blake2Round.Proofs.SeedCallInputs data.workerProjection (Delegation.Caller.workerCells cells) flags := by
    refine ⟨boundary.toSeed, inputs.tables, inputs.family, ?_, inputs.prefixScope.2, ?_⟩
    · intro token present code
      rw [Delegation.Proofs.rv_seed_word boundary present code inputs.controlStart]
      have flagBound := flags.isLt
      simp [Word.ofBitVec, Blake2Round.controlAt, limbBase, BitVec.toNat_ofNat, Delegation.Caller.HashSpan.controlStart]
      omega
    · intro empty
      apply nonempty
      apply List.filter_eq_nil_iff.mpr
      intro row member
      have projected : row ∈ data.workerProjection.rows := member
      rw [empty] at projected
      cases projected
  have masks := Blake2Round.Proofs.matching_masks hp projected (seed.toMatching hp projected)
  intro row member
  exact masks row member

theorem rv_hash_window_memory_inputs [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : RVRequestTrace p} {before : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : RVMixedMemoryAccepted data [])
    (inputs : RVJointHashWindowInputs data before addresses cells span lower upper)
    (requests : RVRequestBinding data before) : RVMixedMemoryInputs data [] before addresses [] cells := by
  refine ⟨inputs.publicProgram, rfl, inputs.initialization, inputs.distinct, inputs.aligned,
    inputs.setup, inputs.tables, ?_⟩
  intro row member family
  cases span with
  | blakeG reduced =>
    have actual := inputs.family row member
    change row.family = .blakeG at actual
    rw [actual] at family
    cases family
  | blakeRound flags => exact rv_round_window_masks hp accepted inputs requests row member
  | keccak =>
    have actual := inputs.family row member
    change row.family = .keccak at actual
    rw [actual] at family
    cases family

theorem rv_joint_entry_control [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : RVRequestTrace p} {before atStart : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    {span : Delegation.Caller.HashSpan} {lower upper : Nat} {start : List (MemoryToken p)}
    (accepted : RVMixedMemoryAccepted data []) (inputs : RVJointHashWindowInputs data before addresses cells span lower upper)
    (requests : RVRequestBinding data before) (prior : Delegation.MemoryAccepted (data.prefixProjection lower start))
    (history : Delegation.RVTraceMapping (data.prefixProjection lower start) before atStart (Delegation.Caller.workerCells cells))
    :
    (Cell.register span.controlRegister).readRV atStart = some span.controlStart := by
  cases span with
  | blakeG reduced =>
    change (Cell.register 12).readRV atStart = some (if reduced then 128 else 0)
    have projected := rv_worker_projection_accepted accepted requests
    have initialized := rv_worker_projection_inputs inputs.initialization inputs.distinct requests
    have nonempty : data.workers.windowRows lower upper ≠ [] := by
      intro empty
      have count := inputs.calls
      rw [empty] at count
      cases reduced <;> simp [Delegation.Caller.HashSpan.callCount, Blake2G.callCount] at count
    obtain ⟨row, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    have member : row ∈ data.workerProjection.rows := List.mem_of_mem_filter present
    have port : Blake2G.importedConstraintsMemoryPorts[8] ∈ row.ports := by
      simp [Delegation.Row.ports, inputs.family row member, Delegation.Caller.HashSpan.family,
        Blake2G.importedConstraintsMemoryPorts]
    have tracked := Delegation.Proofs.seed_port_initialized_cell hp projected
      initialized.toRVBoundaryInputs.toSeed member port (cell := .register 12) (by rfl)
    have prefixMemory : Delegation.RVMemoryInputs (data.prefixProjection lower start) before (Delegation.Caller.workerCells cells) :=
      ⟨initialized.initialization, initialized.distinct,
        fun row member => (requests.clocks row (List.mem_of_mem_filter member)).2,
        fun row member => (requests.clocks row (List.mem_of_mem_filter member)).1.2⟩
    have prefixBoundary := prefixMemory.toRVBoundaryInputs
    have pool : Blake2G.Proofs.SeedControlPoolInputs (data.prefixProjection lower start) (Delegation.Caller.workerCells cells) reduced := by
      refine ⟨prefixBoundary.toSeed, inputs.tables, ?_, ?_, tracked, ?_⟩
      · intro row member
        exact inputs.family row (List.mem_of_mem_filter member)
      · intro row member
        have family := inputs.family row (List.mem_of_mem_filter member)
        simpa [Delegation.Row.columns, Delegation.Caller.HashSpan.family, family,
          Blake2G.importedConstraintsDelegationColumns, Blake2G.Variables.execute]
          using accepted.workerActive row (List.mem_of_mem_filter member)
      · intro token present code
        rw [Delegation.Proofs.rv_seed_word prefixBoundary present code inputs.controlStart]
        cases reduced <;> rfl
    obtain ⟨_, _, _, _, sink, sinkMember, sinkCode, sinkWord⟩ := Blake2G.Proofs.seed_pool_ordered_controls hp prior pool
    obtain ⟨control, _, code, read⟩ := history.finalCells sink sinkMember
    have equal := cell_address_injective (code.trans sinkCode)
    subst control
    have complete : (data.workers.prefixRows lower).length % Blake2G.callCount reduced = 0 := inputs.prefixScope
    have reset : sink.word.toBitVec = if reduced then 128 else 0 := by
      rw [sinkWord]
      simp only [Blake2G.controlAt, RVRequestTrace.prefixProjection, complete, Nat.add_zero]
      cases reduced <;> rfl
    change (Cell.register 12).readRV atStart = some sink.word.toBitVec at read
    rw [read, reset]
  | blakeRound flags =>
    obtain ⟨events, permutation, actual⟩ := history.history
    have empty : (data.prefixProjection lower start).steps = [] := by
      simp only [RVRequestTrace.prefixProjection, Delegation.MemoryData.steps, inputs.prefixScope.1, List.flatMap_nil]
    rw [empty, List.map_nil] at permutation
    have noEvents : events = [] := by
      cases events with
      | nil => rfl
      | cons event rest =>
        have count := permutation.length_eq
        simp at count
    subst events
    cases actual
    exact inputs.controlStart
  | keccak =>
    obtain ⟨events, permutation, actual⟩ := history.history
    have emptyRows : data.workers.prefixRows lower = [] := inputs.prefixScope
    have empty : (data.prefixProjection lower start).steps = [] := by
      simp only [RVRequestTrace.prefixProjection, Delegation.MemoryData.steps, emptyRows, List.flatMap_nil]
    rw [empty, List.map_nil] at permutation
    have noEvents : events = [] := by
      cases events with
      | nil => rfl
      | cons event rest =>
        have count := permutation.length_eq
        simp at count
    subst events
    cases actual
    exact inputs.controlStart

theorem rv_joint_hash_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : RVMixedMemoryAccepted data [])
    (inputs : RVJointHashWindowInputs data before addresses cells span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) :
    RVJointHashWindowResult data before cells span lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have requests := rv_request_binding size clockInverse accepted.toRVRequestChecks inputs.publicProgram
  have memoryInputs := rv_hash_window_memory_inputs size accepted inputs requests
  have projection := rv_projected_window (by omega) clockInverse rotationInverse accepted memoryInputs first last positive ordered
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm, firstHistory, spanHistory,
    startBoundary, finishBoundary, prior, priorHistory, selected, initialized, finalBoundary, target⟩ := projection.execution
  have control := rv_joint_entry_control size accepted inputs requests prior priorHistory
  have protocol : Delegation.Caller.HashSpan.RVProtocol (data.windowProjection lower upper start finish) atStart span :=
    ⟨inputs.tables, fun row member => inputs.family row (List.mem_of_mem_filter member), control, inputs.calls⟩
  have result := rv_hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target finalBoundary.1.addresses
  exact ⟨projection.requests,
    (Delegation.Caller.Proofs.window_call_count projection.requests).trans inputs.calls,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm, firstHistory, spanHistory,
    startBoundary, finishBoundary, selected, initialized, result⟩

end Airbender.UnifiedReduced.Caller.Proofs
