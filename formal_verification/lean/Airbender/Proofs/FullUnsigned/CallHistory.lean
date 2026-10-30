import Airbender.Proofs.FullUnsigned.CallerPorts
import Airbender.Proofs.Delegation.SailHistory
import Airbender.Proofs.Keccak.SplitNonzeroPorts
import Airbender.Proofs.Trace.HistoryWindow

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem worker_window_history (low : Nat)
    {cells : List Cell} {events allEvents cpuEvents workerEvents : List MemoryAccess}
    {initial finalState : State}
    (permutation : events.Perm allEvents)
    (group : (allEvents.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)) =
      cpuEvents ++ workerEvents)
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (cpuZero : ∀ event ∈ cpuEvents, event.2.1 = (Cell.register 0).addressCode)
    (workerNonzero : ∀ event ∈ workerEvents, event.2.1 ≠ (Cell.register 0).addressCode) :
    ∃ before after,
      SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) initial before ∧
      SailHistory cells ((events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).filter
        fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after ∧
      ((events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).filter
        fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).Perm workerEvents ∧
      SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  obtain ⟨before, after, _, past, current, future⟩ := history_window ordered history (by omega : low ≤ low + 4)
  have grouped := (permutation.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).trans
    (List.Perm.of_eq group)
  have cpuRemoved : (cpuEvents.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member selected
    exact (of_decide_eq_true selected) (cpuZero event member)
  have workerKept : (workerEvents.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) =
      workerEvents := List.filter_eq_self.mpr (fun event member => decide_eq_true (workerNonzero event member))
  have actual := grouped.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)
  rw [List.filter_append, cpuRemoved, workerKept, List.nil_append] at actual
  exact ⟨before, after, past, history_without_zero current, actual, future⟩

variable [Fact babyBearModulus.Prime]

/-- The shared native history supplies a standard worker's exact Sail
memory effect between its caller boundaries. Public decoding removes x0 only. -/
theorem unrolled_full_standard_caller_history
    {initial origin finalState : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Delegation.Row babyBearModulus) (present : worker ∈ workers.rows)
    (matched : Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment)
    {cells : List Cell} {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events origin finalState) :
    let low := (decodeTimestamp row.assignment row.columns.initialTime).value
    ∃ before after,
      SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) origin before ∧
      SailHistory cells ((events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).filter
        fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after ∧
      ((events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).filter
        fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).Perm (worker.memorySteps.map transferEvent) ∧
      SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  have group := unrolled_full_standard_caller_events accepted equations active initialClock initialAligned
    row member family selected worker present matched
  apply worker_window_history _ permutation group ordered history
  · intro event included
    unfold machineEvents at included
    obtain ⟨port, physical, rfl⟩ := List.mem_map.mp included
    exact unrolled_full_caller_zero_ports setup lookup accepted excluded initialPC row member family selected
      port (by simpa using physical)
  · intro event included
    obtain ⟨edge, physical, rfl⟩ := List.mem_map.mp included
    obtain ⟨port, native, rfl⟩ := List.mem_map.mp physical
    exact Delegation.Proofs.port_not_zero worker (by simpa using native)

/-- The same shared history supplies a split worker's exact Sail memory
effect. Both cache modes retain every actual worker port. -/
theorem unrolled_full_split_caller_history
    {initial origin finalState : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Keccak.Split.Native.Row babyBearModulus) (present : worker ∈ splitWorkers.rows)
    (matched : worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)
    {cells : List Cell} {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events origin finalState) :
    let low := (decodeTimestamp row.assignment row.columns.initialTime).value
    ∃ before after,
      SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) origin before ∧
      SailHistory cells ((events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).filter
        fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after ∧
      ((events.filter fun event => decide (low < event.1 ∧ event.1 ≤ low + 4)).filter
        fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).Perm
          ((worker.memorySteps splitWorkers.cached).map transferEvent) ∧
      SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  have group := unrolled_full_split_caller_events accepted equations active initialClock initialAligned
    row member family selected worker present matched
  apply worker_window_history _ permutation group ordered history
  · intro event included
    unfold machineEvents at included
    obtain ⟨port, physical, rfl⟩ := List.mem_map.mp included
    exact unrolled_full_caller_zero_ports setup lookup accepted excluded initialPC row member family selected
      port (by simpa using physical)
  · intro event included
    obtain ⟨edge, physical, rfl⟩ := List.mem_map.mp included
    obtain ⟨port, native, rfl⟩ := List.mem_map.mp physical
    exact Keccak.Split.Native.Proofs.port_not_zero splitWorkers.cached worker (by simpa using native)

end Airbender.Compiler.MachineTargets.Proofs
