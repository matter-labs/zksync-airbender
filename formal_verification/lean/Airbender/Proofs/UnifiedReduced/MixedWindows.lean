import Airbender.Review.Trace.UnifiedReduced.MixedWindows
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.RequestWindows
import Airbender.Proofs.Delegation.NativeSegments

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem machine_port_offset (row : Trace.Row p UnifiedFamily) {port : MemoryPort}
    (member : port ∈ machinePorts row) : port.clock.offset < 3 := by
  have native := machine_port_native row member
  simp only [Trace.Row.ports, CircuitLayout.ports] at native
  simp [importedConstraintsMemoryPorts] at native
  rcases native with rfl | rfl | rfl
  all_goals decide

theorem instruction_window_clock {clock offset lower upper : Nat}
    (aligned : clock % 4 = 0) (first : lower % 4 = 0) (last : upper % 4 = 0)
    (small : offset < 4) (positive : 0 < lower) (ordered : lower ≤ upper) :
    (lower - 1 < clock + offset ∧ clock + offset ≤ upper - 1) ↔
      (lower ≤ clock ∧ clock < upper) := by omega

theorem worker_windows_shift [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) {lower upper : Nat}
    (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    data.workers.windowRows lower upper = data.workers.windowRows (lower - 1) (upper - 1) := by
  apply List.filter_congr
  intro worker member
  have write := Delegation.Caller.Proofs.worker_write_time (by omega)
    (requests.clocks worker member).1 (requests.clocks worker member).2
  by_cases live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)
  · have bound := live_worker_clock hp inverse accepted inputs requests member live
    have time : worker.writeTime + 1 = workerClock worker := by
      rw [write]
      change ((decodeTimestamp worker.assignment worker.columns.invocation).value + 2) + 1 =
        (decodeTimestamp worker.assignment worker.columns.invocation).value + 3
      omega
    rw [← time] at bound
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · have zero : (Delegation.Requests.fulfillment worker).time = (0, 0) := not_not.mp live
    have time : worker.writeTime = 2 := by simp [write, zero, timeOfPair, Timestamp.value]
    simp only [time]
    simp [Nat.not_lt.mpr pastZero, Nat.not_lt.mpr (by omega : 2 ≤ lower - 1)]

theorem mixed_window_steps [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) (ordered : lower ≤ upper) :
    data.windowSteps lower upper = Transfer.windowSteps (mixedData data) (lower - 1) (upper - 1) := by
  let selected := fun edge : MemoryToken p × MemoryToken p =>
    decide ((timeOfPair edge.2.time).value ≤ upper - 1) && !decide ((timeOfPair edge.2.time).value ≤ lower - 1)
  let steps := fun row : Trace.Row p UnifiedFamily => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have rowFilter : ∀ row ∈ data.machine.rows, (steps row).filter selected =
      if decide (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper)
      then steps row else [] := by
    intro row member
    have clock := clocks row member
    have aligned : Delegation.Caller.startClock row % 4 = 0 := by
      simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
        using clock.2
    have portFilter : ∀ edge ∈ steps row, selected edge =
        decide (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper) := by
      intro edge present
      obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
      have native := machine_port_native row (by simpa using included)
      have bounds := machine_port_offset row (by simpa using included)
      have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
        clock.1 clock.2 (by omega : port.clock.offset < 4)).2
      change (timeOfPair (writeToken row.columns row.assignment port).time).value =
        Delegation.Caller.startClock row + port.clock.offset at time
      simp only [selected, time]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_le]
      exact and_comm.trans (instruction_window_clock aligned first last (by omega) (by omega) ordered)
    by_cases inside : lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper
    · simp only [decide_eq_true inside, if_true]
      exact List.filter_eq_self.mpr (fun edge present => (portFilter edge present).trans (decide_eq_true inside))
    · simp only [decide_eq_false inside, Bool.false_eq_true, if_false]
      apply List.filter_eq_nil_iff.mpr
      intro edge present
      rw [portFilter edge present, decide_eq_false inside]
      exact Bool.false_ne_true
  have machine : (data.windowMachineRows lower upper).flatMap steps =
      (data.machine.rows.flatMap steps).filter selected := by
    rw [List.filter_flatMap]
    calc
      _ = data.machine.rows.flatMap (fun row => if decide
          (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper)
          then steps row else []) := filter_flatMap _ _ _
      _ = data.machine.rows.flatMap (fun row => (steps row).filter selected) :=
        List.flatMap_congr (fun row member => (rowFilter row member).symm)
  have requests := request_binding hp inverse accepted inputs
  have worker := Delegation.Proofs.native_window_steps data.workers (lower - 1) (upper - 1)
  change (data.workers.windowRows (lower - 1) (upper - 1)).flatMap Delegation.Row.memorySteps =
    Transfer.windowSteps (Delegation.Proofs.transferData data.workers) (lower - 1) (upper - 1) at worker
  rw [← worker_windows_shift hp inverse accepted inputs requests first last pastZero] at worker
  simpa only [RequestTrace.windowSteps, Transfer.windowSteps, Transfer.beforeSteps,
    Transfer.afterSteps, mixedData, RequestTrace.mixedSteps, Delegation.MemoryData.steps,
    Delegation.Proofs.transferData, Delegation.Proofs.windowRows,
    List.filter_append, List.filter_filter, steps, selected] using congrArg₂ (fun left right : List (MemoryToken p × MemoryToken p) => left ++ right) machine worker

theorem native_boundary {data : Transfer.Data p} {state : State} {cells : List Cell}
    (inputs : Transfer.NativeInputs data state cells) : NativeBoundary data.initial state cells :=
  ⟨Delegation.Proofs.transfer_boundary_image inputs,
    fun token member => ⟨inputs.words token member, inputs.clocks token member⟩⟩

theorem native_boundary_read {tokens : List (MemoryToken p)} {state : State} {cells : List Cell}
    (boundary : NativeBoundary tokens state cells) {token : MemoryToken p} (member : token ∈ tokens) :
    ∃ cell ∈ cells, cell.addressCode = token.address ∧ cell.read state = .ok token.word.toBitVec state := by
  obtain ⟨cell, present, value, address, read, word⟩ := boundary.1.values token member
  refine ⟨cell, present, address, ?_⟩
  rw [word, Word.ofBitVec_roundtrip]
  exact read

theorem mixed_window_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) (ordered : lower ≤ upper) :
    MixedWindowExecution data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨inputs.initialization, inputs.distinct⟩
  have zeroRules := mixed_zero_rules size clockInverse accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) zeroRules
  have zero : ∀ edge ∈ (mixedData data).steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0 := by
    intro edge member same
    have value := zeroRules edge member same (fun previous present _ address => zeroReads previous present address)
    rw [value]
    rfl
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, earlierFacts, selectedFacts,
      firstPerm, spanPerm, firstHistory, spanHistory, startInputs, finishInputs⟩ :=
    Transfer.split_native_sail_window facts initialized (mixed_write_rules hp rotationInverse accepted inputs)
      (mixed_write_clocks size clockInverse accepted inputs.publicProgram requests) inputs.aligned zero (lower - 1) (upper - 1)
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks inputs.publicProgram first last pastZero ordered]
    at selectedFacts spanPerm startInputs
  have prefixStepsEqual : Transfer.beforeSteps (mixedData data) (lower - 1) = data.prefixSteps lower := by
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [prefixStepsEqual] at earlierFacts firstPerm
  exact ⟨request_windows size clockInverse accepted.toRequestChecks inputs.publicProgram first last pastZero,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm, firstHistory, spanHistory,
    earlierFacts.matching, selectedFacts.matching, native_boundary startInputs, native_boundary finishInputs⟩

end Airbender.UnifiedReduced.Caller.Proofs
