import Slop.UnifiedReduced.RVCaller.MixedWindows

/-! Native x0 writes of the shared unified/worker pool carry zero (from the RV seed and the zero rules); used to drop
    x0 accesses from RV histories (`rv_history_without_zero`). -/

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true

theorem rv_mixed_zero_writes [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : RVMixedMemoryAccepted data program) (inputs : RVMixedMemoryInputs data program before ca oa cells) :
    ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
  have requests := rv_request_binding hp clockInverse accepted.toRVRequestChecks inputs.publicProgram
  have facts := rv_mixed_memory_facts hp clockInverse accepted inputs.publicProgram inputs.initialization requests
  have zeroRules := rv_mixed_zero_rules hp clockInverse accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (rv_initial_zero inputs.initialization) zeroRules
  intro edge member same
  have value := zeroRules edge member same (fun previous present _ address => zeroReads previous present address)
  rw [value]
  rfl

theorem rv_prefix_steps_mixed [Fact p.Prime] {data : RVRequestTrace p} {cut : Nat}
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.prefixSteps cut) : edge ∈ data.mixedSteps :=
  List.mem_of_mem_filter member

theorem rv_window_steps_mixed [Fact p.Prime] {data : RVRequestTrace p} {lower upper : Nat}
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.windowSteps lower upper) : edge ∈ data.mixedSteps := by
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, List.mem_of_mem_filter rowMember, step⟩))
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp worker
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨row, List.mem_of_mem_filter rowMember, by simpa [Delegation.Row.memorySteps] using step⟩))

/-- Events of a permutation of transfer events of zero-writing x0 edges write zero to x0. -/
theorem rv_events_zero {edges : List (MemoryToken p × MemoryToken p)} {events : List MemoryAccess}
    (permutation : events.Perm (edges.map transferEvent))
    (zero : ∀ edge ∈ edges, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0) :
    ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0 := by
  intro event member same
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp member)
  exact zero edge present same

end Airbender.UnifiedReduced.Caller.Proofs
