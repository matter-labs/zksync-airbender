import Airbender.Proofs.FullUnsigned.EventGroups
import Airbender.Proofs.Trace.HistoryWindow

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Delegation.Caller
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Each ordinary full native window supplies the exact three-port history
used by its original family proof. All six CPU families use the same pool. -/
theorem unrolled_full_ordinary_history
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment))
    {cells : List Cell} {events : List MemoryAccess} {origin finalState : Reference.RiscV.Sail.State}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events origin finalState)
    (reads : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps, edge.1.word.Bounded) :
    let low := (decodeTimestamp row.assignment row.columns.initialTime).value
    ∃ before after,
      SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) origin before ∧
      SailHistory cells (rowEvents 1 row).reverse before after ∧
      (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  have notSelected : ¬ (row.family == .addSub && decide (Delegation.Requests.Selected row.assignment)) = true := by
    intro chosen
    have both : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using chosen
    exact ordinary both
  have ports : machinePorts row = row.ports := by simp only [machinePorts, if_neg notSelected]
  have clock := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned row member
  have canonical : machineEvents row = rowEvents 1 row := by
    simp only [machineEvents, rowEvents, nativeRowEvents, ports]
    apply List.map_congr_left
    intro port present
    have native : port ∈ row.ports := by simpa using present
    have time := (write_time (by decide) (base := rawPair row.assignment row.columns.initialTime)
      clock.1 clock.2 (Trace.Proofs.port_offset row port native)).2
    change transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port) =
      ((1 + (port.event row.columns row.assignment).1, port.address.code row.assignment,
        port.readCode row.assignment, port.writeCode row.assignment) : MemoryAccess)
    simp only [transferEvent, readToken, writeToken, MemoryPort.event, decodeTimestamp, timeOfPair, rawPair]
    simp only [timeOfPair, rawPair] at time
    rw [time]
    congr 1
    omega
  have target : (rowEvents 1 row).reverse.Pairwise (fun a b => b.1 < a.1) := by
    have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2] :=
      @ClockLaws.offsets PooledFamily inferInstance babyBearModulus inferInstance inferInstance row
    have descending : (row.ports.toList.reverse.map fun port => port.clock.offset).Pairwise
        (fun a b : Nat => b < a) := by rw [List.map_reverse, offsets]; decide
    have portOrder : row.ports.toList.reverse.Pairwise (fun a b => b.clock.offset < a.clock.offset) :=
      List.pairwise_map.mp descending
    change (row.ports.toList.map _).reverse.Pairwise _
    rw [← List.map_reverse]
    apply List.pairwise_map.mpr
    apply portOrder.imp
    intro a b less
    change 1 + ((decodeTimestamp row.assignment row.columns.initialTime).value + b.clock.offset) <
      1 + ((decodeTimestamp row.assignment row.columns.initialTime).value + a.clock.offset)
    omega
  let low := (decodeTimestamp row.assignment row.columns.initialTime).value
  obtain ⟨before, after, _, past, current, future⟩ := history_window ordered history (by omega : low ≤ low + 4)
  have grouped := (permutation.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).trans
    (List.Perm.of_eq (unrolled_full_ordinary_events accepted equations active initialClock initialAligned
      row member ordinary))
  have projected : (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).Perm
      (rowEvents 1 row).reverse :=
    (canonical ▸ grouped).trans (List.reverse_perm _).symm
  have targetUnique : ((rowEvents 1 row).reverse.map (fun event => event.1)).Nodup :=
    List.pairwise_map.mpr (target.imp (by intro a b less; omega))
  have unique := (projected.map (fun event => event.1)).nodup_iff.mpr targetUnique
  have currentOrder := ordered.sublist
    (show (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).Sublist events from List.filter_sublist)
  have strict : (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).Pairwise
      (fun a b => b.1 < a.1) := (currentOrder.and (List.pairwise_map.mp unique)).imp (by
    intro a b both
    omega)
  have equal := List.Perm.eq_of_pairwise' target strict projected.symm
  refine ⟨before, after, past, equal.symm ▸ current, ?_, future⟩
  intro port native
  have inMachine : (readToken row.assignment port, writeToken row.columns row.assignment port) ∈ pooledSteps trace :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa [ports] using native, rfl⟩⟩
  exact reads _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inMachine))))

end Airbender.Compiler.MachineTargets.Proofs
