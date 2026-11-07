import Airbender.Proofs.FullUnsigned.CPUWindows
import Airbender.Proofs.Trace.MemoryPaths

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem filter_groups {A B : Type} (rows : List A) (group : A → List B)
    (choose : A → Bool) (selected : B → Bool)
    (agreement : ∀ row ∈ rows, ∀ item ∈ group row, selected item = choose row) :
    (rows.filter choose).flatMap group = (rows.flatMap group).filter selected := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
    have tail := ih (fun row member => agreement row (List.mem_cons_of_mem _ member))
    cases chosen : choose first with
    | true =>
      have all : (group first).filter selected = group first := List.filter_eq_self.mpr
        (fun item member => (agreement first List.mem_cons_self item member).trans chosen)
      simpa only [List.filter_cons, chosen, ↓reduceIte, List.flatMap_cons,
        List.filter_append, List.append_eq, all] using congrArg (List.append (group first)) tail
    | false =>
      have none : (group first).filter selected = [] := List.filter_eq_nil_iff.mpr (by
        intro item member picked
        have same := (agreement first List.mem_cons_self item member).symm.trans picked
        rw [chosen] at same
        cases same)
      simpa only [List.filter_cons, chosen, Bool.false_eq_true, if_false, List.flatMap_cons,
        List.filter_append, none, List.nil_append] using tail

variable [Fact babyBearModulus.Prime]

/-- Each instruction window contains exactly its CPU events and the native
worker events selected by its full request. This is an equality of actual
event lists, before the history supplies chronological permutations. -/
theorem unrolled_full_instruction_events
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows) :
    (((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent).filter fun event =>
      decide ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
        event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4)) =
      machineEvents row ++
        ((workers.rows.filter fun worker => decide (row.family = .addSub ∧
          Delegation.Requests.Selected row.assignment ∧
          Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment)).flatMap
            fun worker => worker.memorySteps.map transferEvent) ++
        ((splitWorkers.rows.filter fun worker => decide (row.family = .addSub ∧
          Delegation.Requests.Selected row.assignment ∧
          worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)).flatMap
            fun worker => (worker.memorySteps splitWorkers.cached).map transferEvent) := by
  let rank := fun source : Trace.Row babyBearModulus PooledFamily =>
    (decodeTimestamp source.assignment source.columns.initialTime).value
  let selected := fun event : MemoryAccess => decide (rank row < event.1 ∧ event.1 ≤ rank row + 4)
  have unique := state_clocks_unique (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have cpu := filter_groups trace.rows machineEvents
    (fun source => decide (rank source = rank row)) selected (by
      intro source included event present
      apply Bool.eq_iff_iff.mpr
      simp only [selected, decide_eq_true_eq]
      rw [unrolled_cpu_event_window accepted initialClock initialAligned row source member included event present]
      exact ⟨fun same => congrArg rank same,
        fun same => List.inj_on_of_nodup_map unique included member same⟩)
  have one := key_filter_singleton rank unique member
  rw [one] at cpu
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at cpu
  have standard := filter_groups workers.rows
    (fun worker => worker.memorySteps.map transferEvent)
    (fun worker => decide (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment ∧
      Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment)) selected (by
        intro worker included event present
        apply Bool.eq_iff_iff.mpr
        simp only [selected, decide_eq_true_eq]
        exact unrolled_full_standard_event_window accepted equations active initialClock initialAligned
          worker included event present row member)
  have split := filter_groups splitWorkers.rows
    (fun worker => (worker.memorySteps splitWorkers.cached).map transferEvent)
    (fun worker => decide (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment ∧
      worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)) selected (by
        intro worker included event present
        apply Bool.eq_iff_iff.mpr
        simp only [selected, decide_eq_true_eq]
        exact unrolled_full_split_event_window accepted equations active initialClock initialAligned
          worker included event present row member)
  have events : (unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent =
      trace.rows.flatMap machineEvents ++
        workers.rows.flatMap (fun worker => worker.memorySteps.map transferEvent) ++
        splitWorkers.rows.flatMap (fun worker => (worker.memorySteps splitWorkers.cached).map transferEvent) := by
    simp only [unrolledFullMemoryData, pooledSteps, Delegation.MemoryData.steps,
      Keccak.Split.Native.MemoryData.steps, List.map_append, List.map_flatMap,
      List.map_map, Function.comp_def]
    rfl
  change ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent).filter selected = _
  rw [events, List.filter_append, List.filter_append, ← cpu, ← standard, ← split]

/-- An ordinary instruction window contains only its own actual CPU events.
No standard or split worker can occur in that window. -/
theorem unrolled_full_ordinary_events
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment)) :
    (((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent).filter fun event =>
      decide ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
        event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4)) =
      machineEvents row := by
  have standard : (workers.rows.filter fun worker => decide (row.family = .addSub ∧
      Delegation.Requests.Selected row.assignment ∧
      Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro worker _ chosen
    have selected := of_decide_eq_true chosen
    exact ordinary ⟨selected.1, selected.2.1⟩
  have split : (splitWorkers.rows.filter fun worker => decide (row.family = .addSub ∧
      Delegation.Requests.Selected row.assignment ∧
      worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro worker _ chosen
    have selected := of_decide_eq_true chosen
    exact ordinary ⟨selected.1, selected.2.1⟩
  rw [unrolled_full_instruction_events accepted equations active initialClock initialAligned row member,
    standard, split]
  simp only [List.flatMap_nil, List.append_nil]

end Airbender.Compiler.MachineTargets.Proofs
