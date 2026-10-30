import Airbender.Proofs.FullUnsigned.RequestSchedule
import Airbender.Proofs.Trace.TransferBoundary
import Airbender.Proofs.Delegation.Atomic

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The complete native pool separates every actual standard-worker address.
Exact matching and its initialized boundary exclude duplicate simultaneous writes. -/
theorem unrolled_full_standard_addresses_distinct
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {origin : State} {cells : List Cell}
    (inputs : Transfer.BoundaryInputs (unrolledFullMemoryData trace workers splitWorkers) origin cells)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ workers.rows) :
    (worker.memorySteps.map fun edge => edge.1.address).Nodup := by
  have rawUnique := Transfer.raw_address_clocks_distinct facts inputs
  have nativeSub : ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent).Sublist
      (Transfer.rawEvents (unrolledFullMemoryData trace workers splitWorkers)) :=
    List.sublist_append_right _ _
  have nativeUnique := rawUnique.sublist (nativeSub.map fun event => (event.1, event.2.1))
  have rowSub : worker.memorySteps.Sublist workers.steps := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Delegation.MemoryData.steps]
      using (List.singleton_sublist.mpr member).flatMap Delegation.Row.memorySteps
  have allSub : worker.memorySteps.Sublist (unrolledFullMemoryData trace workers splitWorkers).steps :=
    rowSub.trans ((List.sublist_append_right (pooledSteps trace) workers.steps).trans
      (List.sublist_append_left _ splitWorkers.steps))
  have unique := nativeUnique.sublist ((allSub.map transferEvent).map fun event => (event.1, event.2.1))
  obtain ⟨caller, _, _, _, _, slot⟩ := unrolled_full_standard_worker_slot
    accepted equations active initialClock initialAligned worker member
  have constant : (worker.memorySteps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (worker.memorySteps.map fun edge => edge.1.address).map (fun address => (caller.clock + 4, address)) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro edge present
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
    have time := slot port (by simpa using included)
    exact congrArg (fun stamp => (stamp, (readToken worker.assignment port).address)) time
  rw [constant] at unique
  exact unique.of_map _

/-- A standard worker's actual Sail history supplies every input observation.
No independent address-separation or per-port observation premise is needed. -/
theorem unrolled_full_standard_input_observations
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {origin : State} {cells : List Cell}
    (inputs : Transfer.BoundaryInputs (unrolledFullMemoryData trace workers splitWorkers) origin cells)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ workers.rows)
    {before after : State} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before := by
  have distinct := unrolled_full_standard_addresses_distinct accepted equations active
    initialClock initialAligned facts inputs member
  have eventDistinct : (events.map fun event => event.2.1).Nodup :=
    (permutation.map (fun event => event.2.1)).nodup_iff.mpr (by
      simpa only [List.map_map, Function.comp_def, transferEvent] using distinct)
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp included)
    obtain ⟨port, native, rfl⟩ := List.mem_map.mp present
    exact Delegation.Proofs.port_not_zero worker (by simpa using native)
  have actual := Delegation.Proofs.atomic_observations history aligned noZero readable eventDistinct
  intro port included
  have event := permutation.mem_iff.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr
    ⟨port, by simpa using included, rfl⟩, rfl⟩)
  obtain ⟨cell, _, address, read, _⟩ := actual _ event
  exact ⟨cell, address, read⟩

end Airbender.Compiler.MachineTargets.Proofs
