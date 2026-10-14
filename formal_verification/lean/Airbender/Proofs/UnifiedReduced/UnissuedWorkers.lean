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

end Airbender.UnifiedReduced.Caller.Proofs
