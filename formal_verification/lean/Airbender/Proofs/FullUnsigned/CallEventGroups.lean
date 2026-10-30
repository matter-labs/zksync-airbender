import Airbender.Proofs.FullUnsigned.EventGroups

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem filter_matched_singleton {A : Type} (rows : List A)
    (request : A → Delegation.Requests.Request p)
    (unique : (rows.map fun worker => (request worker).time).Nodup)
    (worker : A) (present : worker ∈ rows) (called : Delegation.Requests.Request p)
    (matched : request worker = called) :
    rows.filter (fun current => decide (request current = called)) = [worker] := by
  have one := key_filter_singleton (fun current => (request current).time) unique present
  calc
    _ = rows.filter (fun current => decide ((request current).time = (request worker).time)) := by
      apply List.filter_congr
      intro current included
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro equal
        exact congrArg Delegation.Requests.Request.time (equal.trans matched.symm)
      · intro equal
        have same : current = worker := List.inj_on_of_nodup_map unique included present equal
        subst current
        exact matched
    _ = [worker] := one

private theorem standard_split_requests_ne (standard : Delegation.Row p)
    (split : Keccak.Split.Native.Row p) (cached : Bool) :
    Delegation.Requests.fulfillment standard ≠ split.fulfillment cached := by
  intro same
  have csr := congrArg Delegation.Requests.Request.csr same
  cases standard with
  | mk family assignment =>
    cases split with
    | mk kind witness =>
      cases family <;> cases kind <;>
        norm_num [Delegation.Requests.fulfillment, Delegation.Requests.csr,
          Keccak.Split.Native.Row.fulfillment, Keccak.Split.Kind.csr] at csr

variable [Fact babyBearModulus.Prime]

/-- A standard caller window contains exactly its own CPU events and the
one matched native worker. No split worker contributes an event. -/
theorem unrolled_full_standard_caller_events
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
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Delegation.Row babyBearModulus) (present : worker ∈ workers.rows)
    (matched : Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment) :
    (((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent).filter fun event =>
      decide ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
        event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4)) =
      machineEvents row ++ worker.memorySteps.map transferEvent := by
  have unique := unrolled_full_fulfillment_times_unique accepted equations active initialClock initialAligned
  simp only [List.map_append, List.map_map, Function.comp_def] at unique
  have standard : (workers.rows.filter fun current => decide (row.family = .addSub ∧
      Delegation.Requests.Selected row.assignment ∧
      Delegation.Requests.fulfillment current = Delegation.Requests.caller row.assignment)) = [worker] := by
    simpa [family, selected] using filter_matched_singleton workers.rows
      Delegation.Requests.fulfillment (unique.sublist (List.sublist_append_left _ _))
      worker present _ matched
  have split : (splitWorkers.rows.filter fun current => decide (row.family = .addSub ∧
      Delegation.Requests.Selected row.assignment ∧
      current.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro current _ chosen
    have equal := (of_decide_eq_true chosen).2.2
    exact standard_split_requests_ne worker current splitWorkers.cached (matched.trans equal.symm)
  rw [unrolled_full_instruction_events accepted equations active initialClock initialAligned row member,
    standard, split]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- A split caller window contains exactly its own CPU events and the one
matched split worker. No standard worker contributes an event. -/
theorem unrolled_full_split_caller_events
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
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Keccak.Split.Native.Row babyBearModulus) (present : worker ∈ splitWorkers.rows)
    (matched : worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment) :
    (((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent).filter fun event =>
      decide ((decodeTimestamp row.assignment row.columns.initialTime).value < event.1 ∧
        event.1 ≤ (decodeTimestamp row.assignment row.columns.initialTime).value + 4)) =
      machineEvents row ++ (worker.memorySteps splitWorkers.cached).map transferEvent := by
  have unique := unrolled_full_fulfillment_times_unique accepted equations active initialClock initialAligned
  simp only [List.map_append, List.map_map, Function.comp_def] at unique
  have standard : (workers.rows.filter fun current => decide (row.family = .addSub ∧
      Delegation.Requests.Selected row.assignment ∧
      Delegation.Requests.fulfillment current = Delegation.Requests.caller row.assignment)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro current _ chosen
    have equal := (of_decide_eq_true chosen).2.2
    exact standard_split_requests_ne current worker splitWorkers.cached (equal.trans matched.symm)
  have split : (splitWorkers.rows.filter fun current => decide (row.family = .addSub ∧
      Delegation.Requests.Selected row.assignment ∧
      current.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)) = [worker] := by
    simpa [family, selected] using filter_matched_singleton splitWorkers.rows
      (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)
      (unique.sublist (List.sublist_append_right _ _)) worker present _ matched
  rw [unrolled_full_instruction_events accepted equations active initialClock initialAligned row member,
    standard, split]
  simp only [List.flatMap_nil, List.flatMap_cons, List.append_nil]

end Airbender.Compiler.MachineTargets.Proofs
