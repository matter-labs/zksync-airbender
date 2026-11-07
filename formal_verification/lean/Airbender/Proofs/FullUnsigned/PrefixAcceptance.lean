import Airbender.Proofs.FullUnsigned.PrefixRequests

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The complete native pool restricts to an accepted prefix and its exact RAM
frontier. Construction uses no worker command, supported argument or reference
execution. The same frontier retains the full suffix matching facts. -/
theorem unrolled_full_prefix_accepted
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ trace.rows)
    (positive : 0 < next.clock) :
    ∃ memory : List (MemoryToken babyBearModulus),
      UnrolledAcceptance (unrolledFullPrefixTrace trace next.start memory)
        (unrolledFullPrefixWorkers workers next.start)
        (unrolledFullPrefixSplitWorkers splitWorkers next.start).steps
        ((unrolledFullPrefixSplitWorkers splitWorkers next.start).rows.map
          (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)) ∧
      Transfer.Facts ⟨memory, trace.terminalMemory,
        Transfer.afterSteps (unrolledFullMemoryData trace workers splitWorkers) (next.clock - 1)⟩ := by
  classical
  obtain ⟨memory, earlier, later⟩ := Transfer.split_at facts (next.clock - 1)
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have states := UnifiedReduced.Caller.Proofs.state_prefix_matching
    (fun state : PCState.State babyBearModulus => (timeOfPair state.timestamp).value)
    Trace.Row.start Trace.Row.finish accepted.states (by
      intro row included
      have advance := ClockLaws.advance (by decide)
        (by decide +kernel : SerializedInverse.Clock babyBearModulus) trace.rom row
        (accepted.cpuEquations row included) (clocks row included).1
      change (timeOfPair row.finish.timestamp).value = row.clock + 4 at advance
      change row.clock < (timeOfPair row.finish.timestamp).value
      omega) member
  refine ⟨memory, ?_, later⟩
  refine {
    cpuEquations := fun row included => accepted.cpuEquations row (List.mem_of_mem_filter included)
    cpuActive := fun row included => accepted.cpuActive row (List.mem_of_mem_filter included)
    workerEquations := fun row included => accepted.workerEquations row (List.mem_of_mem_filter included)
    workerActive := fun row included => accepted.workerActive row (List.mem_of_mem_filter included)
    states := states
    requests := unrolled_full_prefix_requests accepted equations active initialClock initialAligned member memory
    ram := ?_ }
  change (trace.initialMemory ++
    (unrolledFullMemoryData (unrolledFullPrefixTrace trace next.start memory)
      (unrolledFullPrefixWorkers workers next.start) (unrolledFullPrefixSplitWorkers splitWorkers next.start)).steps.map Prod.snd).Perm
    (memory ++ (unrolledFullMemoryData (unrolledFullPrefixTrace trace next.start memory)
      (unrolledFullPrefixWorkers workers next.start) (unrolledFullPrefixSplitWorkers splitWorkers next.start)).steps.map Prod.fst)
  rw [unrolled_full_prefix_steps accepted initialClock initialAligned member positive memory]
  exact earlier.matching

end Airbender.Compiler.MachineTargets.Proofs
