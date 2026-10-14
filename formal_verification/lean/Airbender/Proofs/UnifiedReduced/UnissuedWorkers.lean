import Airbender.Review.Trace.UnifiedReduced.UnissuedWorkers
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.RequestWindows
import Airbender.Proofs.Blake2Round.ExclusiveMask

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem first_machine_port (row : Trace.Row p UnifiedFamily) :
    importedConstraintsMemoryPorts[0] ∈ machinePorts row := by
  unfold machinePorts
  split
  · simp [architecturalPorts]
  · cases row with
    | mk kind w => cases kind; simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]

/-- The mandatory offset-zero access has a strictly earlier read. Native
    four-alignment therefore places every machine row at clock four or later,
    even when no positive public initial-clock premise is supplied. -/
theorem machine_native_clock_positive [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (image : initialImage before cells = some data.machine.initialMemory)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) :
    4 ≤ Delegation.Caller.startClock row := by
  have requests := request_binding hp inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts hp inverse accepted publicProgram image requests
  have first := first_machine_port row
  have positive := facts.order _ (mixed_machine_member member first)
  have time := mixed_machine_time_of_program hp inverse accepted publicProgram member
    (machine_port_native row first)
  have alignment := (machine_clock_facts hp inverse accepted.toRequestChecks publicProgram member).1
  have base : (timeOfPair (writeToken row.columns row.assignment importedConstraintsMemoryPorts[0]).time).value =
      Delegation.Caller.startClock row := by
    simpa [MemoryPort.event, importedConstraintsMemoryPorts, Delegation.Caller.startClock, Trace.Row.clock] using time
  rw [base] at positive
  omega

/-- Every produced architectural token is at clock two or later. The mandatory
    first machine access and native alignment derive positive machine clocks. -/
theorem mixed_write_floor [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (image : initialImage before cells = some data.machine.initialMemory) :
    ∀ edge ∈ data.mixedSteps, 2 ≤ (timeOfPair edge.2.time).value := by
  have requests := request_binding hp inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts hp inverse accepted publicProgram image requests
  intro edge edgeMember
  rcases List.mem_append.mp edgeMember with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have first := first_machine_port row
    have source := mixed_machine_member rowMember first
    have positive := facts.order _ source
    have initialTime := mixed_machine_time_of_program hp inverse accepted publicProgram rowMember
      (machine_port_native row first)
    have currentTime := mixed_machine_time_of_program hp inverse accepted publicProgram rowMember
      (machine_port_native row (by simpa using portMember))
    have alignment := (machine_clock_facts hp inverse accepted.toRequestChecks publicProgram rowMember).1
    have base : (timeOfPair (writeToken row.columns row.assignment importedConstraintsMemoryPorts[0]).time).value =
        Delegation.Caller.startClock row := by
      simpa [MemoryPort.event, importedConstraintsMemoryPorts, Delegation.Caller.startClock, Trace.Row.clock] using initialTime
    have time : (timeOfPair (writeToken row.columns row.assignment port).time).value =
        Delegation.Caller.startClock row + port.clock.offset := by
      simpa [MemoryPort.event, Delegation.Caller.startClock, Trace.Row.clock] using currentTime
    rw [base] at positive
    change 2 ≤ (timeOfPair (writeToken row.columns row.assignment port).time).value
    rw [time]
    omega
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native : port ∈ row.ports := by simpa using portMember
    have time := Delegation.Caller.Proofs.worker_write_time (by omega)
      (requests.clocks row rowMember).1 (requests.clocks row rowMember).2
    have same : (row.writeToken port).time =
        ((rawPair row.assignment row.columns.invocation).1 + 2,
          (rawPair row.assignment row.columns.invocation).2) := by
      simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset row native, Nat.cast_ofNat]
    change 2 ≤ (timeOfPair (row.writeToken port).time).value
    rw [same]
    change 2 ≤ row.writeTime
    omega

theorem unissued_initial_reads [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (image : initialImage before cells = some data.machine.initialMemory)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    (zero : (Delegation.Requests.fulfillment worker).time = (0, 0)) :
    InitialWorkerReads before cells worker := by
  have requests := request_binding hp inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts hp inverse accepted publicProgram image requests
  have floors := mixed_write_floor hp inverse accepted publicProgram image
  intro port native
  have source := mixed_worker_member member native
  have time := Delegation.Caller.Proofs.worker_write_time (by omega)
    (requests.clocks worker member).1 (requests.clocks worker member).2
  have clock : worker.writeTime = 2 := by simpa [zero, timeOfPair, Timestamp.value] using time
  have same : (worker.writeToken port).time =
      ((rawPair worker.assignment worker.columns.invocation).1 + 2,
        (rawPair worker.assignment worker.columns.invocation).2) := by
    simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset worker native, Nat.cast_ofNat]
  have current : (timeOfPair (worker.writeToken port).time).value = 2 := by
    rw [same]
    exact clock
  have matched := facts.matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, source, rfl⟩)))
  rcases List.mem_append.mp matched with initial | produced
  · exact image_sources image _ initial
  · obtain ⟨previous, present, equal⟩ := List.mem_map.mp produced
    have lower := floors previous present
    have upper := facts.order _ source
    rw [equal] at lower
    rw [current] at upper
    omega

theorem unissued_round_initial_control [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (image : initialImage before cells = some data.machine.initialMemory)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    (family : worker.family = .blakeRound)
    (zero : (Delegation.Requests.fulfillment worker).time = (0, 0)) :
    InitialRoundControl before worker := by
  have reads := unissued_initial_reads hp inverse accepted publicProgram image member zero
  cases worker with
  | mk kind w =>
    change kind = .blakeRound at family
    subst kind
    let port := Blake2Round.importedConstraintsMemoryPorts[42]
    have native : port ∈ (Delegation.Row.mk .blakeRound w).ports := by
      simp [port, Delegation.Row.ports, Blake2Round.importedConstraintsMemoryPorts]
    obtain ⟨cell, _, value, read, equal⟩ := reads port native
    have address : cell.addressCode = (Cell.register 12).addressCode :=
      (congrArg MemoryToken.address equal).symm
    have same := cell_address_injective address
    subst cell
    have high := congrArg (fun token : MemoryToken p => token.word.hi) equal
    have high : (w Blake2Round.Variables.controlReadHi).val = (Word.ofBitVec value).hi := by
      simpa [readToken, MemoryToken.word, port, Blake2Round.importedConstraintsMemoryPorts,
        MemoryPort.readCode, WordColumns.code, pairCode, Cell.initialToken,
        Blake2Round.Variables.controlReadHi] using high
    have core := Verification.holds_of_sublist (accepted.workerConstraints _ member)
      (List.sublist_append_left (Blake2Round.importedConstraints data.workers.setup.blakeRound)
        Blake2Round.importedConstraintsTimestampLookups)
    refine ⟨value, read, ?_⟩
    intro round
    simpa only [high] using (Blake2Round.Proofs.exclusive_mask_iff (by dsimp [timestampBase] at hp; omega) core round)

private def pointerPort (worker : Delegation.Row p) : MemoryPort :=
  match worker.family with
  | .bigint => Bigint.importedConstraintsMemoryPorts[0]
  | .blakeG => Blake2G.importedConstraintsMemoryPorts[0]
  | .blakeRound => Blake2Round.importedConstraintsMemoryPorts[0]
  | .keccak => Keccak.importedConstraintsMemoryPorts[0]

private theorem pointer_port_member (worker : Delegation.Row p) : pointerPort worker ∈ worker.ports := by
  cases worker with
  | mk kind w =>
    cases kind <;> simp only [pointerPort, Delegation.Row.ports]
    all_goals exact Array.getElem_mem (by decide)

private theorem pointer_port_address (worker : Delegation.Row p) :
    (pointerPort worker).address = .constantRegister 10 := by
  cases worker with
  | mk kind w => cases kind <;> rfl

private def pointerStep (worker : Delegation.Row p) : MemoryToken p × MemoryToken p :=
  (readToken worker.assignment (pointerPort worker), worker.writeToken (pointerPort worker))

private theorem pointer_step_member (worker : Delegation.Row p) : pointerStep worker ∈ worker.memorySteps :=
  List.mem_map.mpr ⟨pointerPort worker, by simpa using pointer_port_member worker, rfl⟩

private theorem pointer_steps_sublist (workers : List (Delegation.Row p)) :
    (workers.map pointerStep).Sublist (workers.flatMap Delegation.Row.memorySteps) := by
  induction workers with
  | nil => exact List.Sublist.refl _
  | cons worker rest ih =>
    exact (List.singleton_sublist.mpr (pointer_step_member worker)).append ih

/-- Every family transfers x10 at its invocation plus two. Initialized memory
    uniqueness therefore distinguishes all worker clocks, including unissued
    clocks, without assuming any operation mask or valid control. -/
theorem worker_invocation_uniqueness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (image : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup) : WorkerInvocationUniqueness data := by
  have requests := request_binding hp inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts hp inverse accepted publicProgram image requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨image, distinct⟩
  have rawUnique := Transfer.raw_address_clocks_distinct facts initialized.toBoundaryInputs
  have eventsSub : (data.mixedSteps.map transferEvent).Sublist (Transfer.rawEvents (mixedData data)) :=
    List.sublist_append_right _ _
  have keys := rawUnique.sublist (eventsSub.map fun event => (event.1, event.2.1))
  have stepsSub : (data.workers.rows.map pointerStep).Sublist data.mixedSteps :=
    (pointer_steps_sublist data.workers.rows).trans (List.sublist_append_right _ _)
  have selected := keys.sublist ((stepsSub.map transferEvent).map fun event => (event.1, event.2.1))
  have constant : ((data.workers.rows.map pointerStep).map transferEvent).map (fun event => (event.1, event.2.1)) =
      (data.workers.rows.map workerClock).map (fun clock => (clock, (Cell.register 10).addressCode)) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro worker member
    have time := worker_event_clock (by omega) requests member
      (List.mem_map.mpr ⟨pointerStep worker, pointer_step_member worker, rfl⟩)
    apply Prod.ext
    · exact time
    · change (pointerPort worker).address.code worker.assignment = (Cell.register 10).addressCode
      rw [pointer_port_address]
      rfl
  rw [constant] at selected
  have workers := selected.of_map (fun clock => (clock, (Cell.register 10).addressCode))
  have shifted : ((data.workers.rows.map fun worker =>
      (timeOfPair (Delegation.Requests.fulfillment worker).time).value).map (fun clock => clock + 3)).Nodup := by
    rw [List.map_map]
    change (data.workers.rows.map workerClock).Nodup
    exact workers
  have clocks := shifted.of_map (fun clock => clock + 3)
  have raw : (data.workers.rows.map fun worker => (Delegation.Requests.fulfillment worker).time).Nodup :=
    List.Nodup.of_map (fun time => (timeOfPair time).value) (by
      simpa only [List.map_map, Function.comp_def] using clocks)
  let unissued := data.workers.rows.filter fun worker => decide ((Delegation.Requests.fulfillment worker).time = (0, 0))
  have narrowed : (unissued.map fun worker => (Delegation.Requests.fulfillment worker).time).Nodup :=
    raw.sublist (List.filter_sublist.map _)
  have zeros : (unissued.map fun worker => (Delegation.Requests.fulfillment worker).time) =
      List.replicate unissued.length (0, 0) := by
    apply List.map_eq_replicate_iff.mpr
    intro worker member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  rw [zeros] at narrowed
  exact ⟨clocks, raw, List.nodup_replicate.mp narrowed⟩

end Airbender.UnifiedReduced.Caller.Proofs
