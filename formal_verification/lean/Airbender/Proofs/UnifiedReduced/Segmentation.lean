import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.UnifiedReduced.Segmentation
import Airbender.Proofs.UnifiedReduced.ComputedRoundRegions

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem ordered_hash_window_bounds {windows : List HashWindow} {cut : Nat}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval)) :
    (∀ window ∈ windows, cut ≤ window.lower ∧ window.lower ≤ window.upper ∧
      window.lower % 4 = 0 ∧ window.upper % 4 = 0) ∧
    windows.Pairwise (fun first second => first.upper ≤ second.lower) := by
  induction windows generalizing cut with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨lower, extent, first, last, rest⟩ := ordered
    obtain ⟨bounds, separated⟩ := ih rest
    constructor
    · intro window member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨lower, extent, first, last⟩
      · obtain ⟨after, extent', first', last'⟩ := bounds window member
        exact ⟨by omega, extent', first', last'⟩
    · exact List.pairwise_cons.mpr ⟨fun window member => (bounds window member).1, separated⟩

theorem ordered_hash_window_unique {windows : List HashWindow} {cut time : Nat}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    {first second : HashWindow} (one : first ∈ windows) (two : second ∈ windows)
    (firstRange : first.lower < time ∧ time ≤ first.upper)
    (secondRange : second.lower < time ∧ time ≤ second.upper) : first = second := by
  induction windows generalizing cut with
  | nil => cases one
  | cons head tail ih =>
    obtain ⟨_, _, _, _, rest⟩ := ordered
    have bounds := (ordered_hash_window_bounds rest).1
    rcases List.mem_cons.mp one with firstHead | firstTail
    · rcases List.mem_cons.mp two with secondHead | secondTail
      · exact firstHead.trans secondHead.symm
      · rw [firstHead] at firstRange
        have := (bounds second secondTail).1
        omega
    · rcases List.mem_cons.mp two with secondHead | secondTail
      · rw [secondHead] at secondRange
        have := (bounds first firstTail).1
        omega
      · exact ih rest firstTail secondTail

open Classical in
theorem disjoint_filter_flatMap_count {α β : Type} [BEq α] [LawfulBEq α] (rows : List α) (windows : List β)
    (select : β → α → Bool)
    (separated : windows.Pairwise (fun first second => ∀ row,
      ¬ (select first row = true ∧ select second row = true))) (row : α) :
    (windows.flatMap fun window => rows.filter (select window)).count row =
      if ∃ window ∈ windows, select window row = true then rows.count row else 0 := by
  classical
  induction windows with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨disjoint, rest⟩ := List.pairwise_cons.mp separated
    rw [List.flatMap_cons, List.count_append, ih rest]
    by_cases chosen : select head row = true
    · have absent : ¬ ∃ window ∈ tail, select window row = true := by
        rintro ⟨window, member, selected⟩
        exact disjoint window member row ⟨chosen, selected⟩
      rw [List.count_filter chosen]
      simp [chosen, absent]
    · have zero : (rows.filter (select head)).count row = 0 := by
        apply List.count_eq_zero.mpr
        simp [chosen]
      rw [zero]
      simp [chosen]

theorem program_hash_worker_coverage [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {windows : List HashWindow}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (cuts : ∀ window ∈ windows, window.lower % 4 = 0 ∧ window.upper % 4 = 0 ∧ 2 ≤ window.lower)
    (coverage : ProgramHashCallerCoverage data windows) :
    ∀ worker ∈ data.workers.rows, worker.family ≠ .bigint →
      ((∃ window ∈ windows, worker ∈ data.workers.windowRows window.lower window.upper) ↔
        Delegation.Requests.Live (Delegation.Requests.fulfillment worker)) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have binding := request_binding size clockInverse accepted.toRequestChecks publicProgram
  have pcClock := wrapped_program_pc_clock hp clockInverse setup accepted publicProgram ordinaryProgram registry
  have clocks := state_clock_inputs size clockInverse accepted.constraints accepted.states
    publicProgram.initialClock publicProgram.initialAligned
  have intervals := state_clock_interval size clockInverse accepted.constraints accepted.states
    publicProgram.initialClock publicProgram.initialAligned
  intro worker member family
  constructor
  · rintro ⟨window, included, inside⟩ zero
    have cut := cuts window included
    have requests := request_windows size clockInverse accepted.toRequestChecks publicProgram cut.1 cut.2.1 cut.2.2
    exact (requests.unissued worker member zero).2 inside
  · intro live
    have fulfilled : Delegation.Requests.fulfillment worker ∈
        data.fulfillments.filter (fun call => decide (Delegation.Requests.Live call)) :=
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨worker, member, rfl⟩, decide_eq_true live⟩
    obtain ⟨caller, callerMember, same⟩ := List.mem_map.mp (binding.fulfilled.mem_iff.mpr fulfilled)
    have decoded := accepted.decoded caller callerMember
    change ∃ i : Fin data.program.length, caller.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
    obtain ⟨i, query⟩ := decoded
    let entry := data.program.get i
    have entryFamily : entry.data.family = worker.family :=
      (matched_caller_entry_family (by omega) query same.symm).symm
    have machineMember := List.mem_of_mem_filter callerMember
    have pc := caller_query_pc_word (by dsimp [limbBase]; omega) query
    have clock := pcClock caller machineMember
    rw [pc, Word.ofBitVec_roundtrip] at clock
    have bounds := intervals caller machineMember
    have alignment : Delegation.Caller.startClock caller % 4 = 0 := by
      simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
        using (clocks caller machineMember).2
    obtain ⟨window, included, lower, upper, _⟩ := coverage entry (List.get_mem _ _)
      (entryFamily ▸ family) (Delegation.Caller.startClock caller) bounds.1 bounds.2 alignment clock
    have inside : caller ∈ Delegation.Caller.windowCallers data.callers window.lower window.upper :=
      List.mem_filter.mpr ⟨callerMember, decide_eq_true ⟨lower, upper⟩⟩
    have cut := cuts window included
    have requests := request_windows size clockInverse accepted.toRequestChecks publicProgram cut.1 cut.2.1 cut.2.2
    obtain ⟨selected, selectedMatch, _⟩ := requests.callerMatches caller inside
    obtain ⟨chosen, _, unique⟩ := Delegation.Requests.Proofs.unique_fulfillment binding.fulfilled binding.invocations.1
      (List.mem_map.mpr ⟨caller, callerMember, rfl⟩)
    have equal : worker = selected :=
      (unique worker ⟨member, same.symm⟩).trans
        (unique selected ⟨List.mem_of_mem_filter selectedMatch.1, selectedMatch.2.1⟩).symm
    exact ⟨window, included, equal.symm ▸ selectedMatch.1⟩

theorem hash_worker_partition [Fact p.Prime]
    {data : RequestTrace p} {windows : List HashWindow}
    (separated : windows.Pairwise (fun first second => first.upper ≤ second.lower))
    (families : ∀ window ∈ windows, ∀ worker ∈ data.workers.windowRows window.lower window.upper,
      worker.family = window.span.family)
    (covered : ∀ worker ∈ data.workers.rows, worker.family ≠ .bigint →
      ((∃ window ∈ windows, worker ∈ data.workers.windowRows window.lower window.upper) ↔
        Delegation.Requests.Live (Delegation.Requests.fulfillment worker))) :
    (windows.flatMap fun window => data.workers.windowRows window.lower window.upper).Perm
      (issuedHashWorkers data) := by
  classical
  let select (window : HashWindow) (worker : Delegation.Row p) :=
    decide (window.lower < worker.writeTime ∧ worker.writeTime ≤ window.upper)
  have disjoint : windows.Pairwise (fun first second => ∀ worker,
      ¬ (select first worker = true ∧ select second worker = true)) := by
    apply separated.imp
    intro first second order worker both
    have firstRange := of_decide_eq_true both.1
    have secondRange := of_decide_eq_true both.2
    omega
  apply List.perm_iff_count.mpr
  intro worker
  have count := disjoint_filter_flatMap_count data.workers.rows windows select disjoint worker
  change (windows.flatMap fun window => data.workers.windowRows window.lower window.upper).count worker =
    (if ∃ window ∈ windows, select window worker = true then data.workers.rows.count worker else 0) at count
  rw [count]
  by_cases member : worker ∈ data.workers.rows
  · have selection : (∃ window ∈ windows, select window worker = true) ↔
        worker.family ≠ .bigint ∧ Delegation.Requests.Live (Delegation.Requests.fulfillment worker) := by
      constructor
      · rintro ⟨window, included, selected⟩
        have inside : worker ∈ data.workers.windowRows window.lower window.upper := List.mem_filter.mpr ⟨member, selected⟩
        have family := families window included worker inside
        have hash : worker.family ≠ .bigint := by
          rw [family]
          cases window.span <;> simp [Delegation.Caller.HashSpan.family]
        exact ⟨hash, (covered worker member hash).mp ⟨window, included, inside⟩⟩
      · rintro ⟨hash, live⟩
        obtain ⟨window, included, inside⟩ := (covered worker member hash).mpr live
        exact ⟨window, included, (List.mem_filter.mp inside).2⟩
    by_cases wanted : worker.family ≠ .bigint ∧ Delegation.Requests.Live (Delegation.Requests.fulfillment worker)
    · rw [if_pos (selection.mpr wanted)]
      simpa only [issuedHashWorkers] using (List.count_filter
        (p := fun actual : Delegation.Row p => decide
          (actual.family ≠ .bigint ∧ Delegation.Requests.Live (Delegation.Requests.fulfillment actual)))
        (a := worker) (l := data.workers.rows) (decide_eq_true wanted)).symm
    · rw [if_neg (fun selected => wanted (selection.mp selected))]
      symm
      apply List.count_eq_zero.mpr
      simp [issuedHashWorkers, wanted]
  · have absent : worker ∉ issuedHashWorkers data := fun inside => member (List.mem_of_mem_filter inside)
    rw [List.count_eq_zero.mpr member, List.count_eq_zero.mpr absent]
    split <;> rfl

theorem program_hash_segmentation [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {windows : List HashWindow} {cut : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ProtocolContextInputs data before ca oa cells program) (registry : WrappedSequentialProgram program)
    (scopes : ∀ window ∈ windows, WrappedProgramComputedProtocolWindowInputs data program window)
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    (coverage : ProgramHashCallerCoverage data windows) : IssuedHashSegmentation data windows := by
  have bounds := (ordered_hash_window_bounds ordered).1
  have cuts : ∀ window ∈ windows, window.lower % 4 = 0 ∧ window.upper % 4 = 0 ∧ 2 ≤ window.lower := by
    intro window member
    have bound := bounds window member
    have floor := hash_control_preparation_after_initial (scopes window member).preparation
    exact ⟨bound.2.2.1, bound.2.2.2, by omega⟩
  have localScope : ∀ window ∈ windows, ComputedProtocolWindowInputs data program window := by
    intro window member
    exact wrapped_program_computed_protocol_window_inputs hp clockInverse inputs.setup accepted inputs.publicProgram
      inputs.ordinaryProgram registry (scopes window member) (cuts window member).1 (cuts window member).2.1
  have covered := program_hash_worker_coverage hp clockInverse inputs.setup accepted inputs.publicProgram
    inputs.ordinaryProgram registry cuts coverage
  have families := fun window member => (localScope window member).family
  have partition := hash_worker_partition (ordered_hash_window_bounds ordered).2 families covered
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests : ∀ window ∈ windows,
      Delegation.Caller.RequestWindowBinding data.callers data.workers window.lower window.upper := by
    intro window member
    have cut := cuts window member
    exact request_windows size clockInverse accepted.toRequestChecks inputs.publicProgram cut.1 cut.2.1 cut.2.2
  refine ⟨partition, ?_, ?_, ?_, ?_⟩
  · intro worker member family live
    obtain ⟨window, included, inside⟩ := (covered worker member family).mpr live
    refine ⟨window, ⟨included, inside⟩, ?_⟩
    intro other otherInside
    have firstRange := of_decide_eq_true (List.mem_filter.mp otherInside.2).2
    have secondRange := of_decide_eq_true (List.mem_filter.mp inside).2
    exact ordered_hash_window_unique ordered otherInside.1 included firstRange secondRange
  · have combined : (windows.flatMap fun window =>
        (Delegation.Caller.windowCallers data.callers window.lower window.upper).map
          (fun caller => Delegation.Requests.caller caller.assignment)).Perm
        (windows.flatMap fun window =>
          (data.workers.windowRows window.lower window.upper).map Delegation.Requests.fulfillment) := by
      have combine : ∀ (list : List HashWindow),
          (∀ window ∈ list, Delegation.Caller.RequestWindowBinding data.callers data.workers window.lower window.upper) →
          (list.flatMap fun window => (Delegation.Caller.windowCallers data.callers window.lower window.upper).map
            (fun caller => Delegation.Requests.caller caller.assignment)).Perm
          (list.flatMap fun window => (data.workers.windowRows window.lower window.upper).map Delegation.Requests.fulfillment) := by
        intro list
        induction list with
        | nil => intro _; exact List.Perm.refl _
        | cons head tail ih =>
          intro available
          exact (available head List.mem_cons_self).fulfilled.append
            (ih (fun window member => available window (List.mem_cons_of_mem _ member)))
      exact combine windows requests
    exact combined.trans (by simpa only [List.map_flatMap] using partition.map Delegation.Requests.fulfillment)
  · have length := partition.length_eq
    rw [List.length_flatMap] at length
    have counts : (windows.map fun window => (data.workers.windowRows window.lower window.upper).length) =
        windows.map (fun window => window.span.callCount) := by
      apply List.map_congr_left
      intro window member
      exact (localScope window member).calls
    rw [counts] at length
    exact length
  · intro worker member family
    have relation := covered worker member family
    constructor
    · intro absent
      by_contra live
      obtain ⟨window, included, inside⟩ := relation.mpr live
      exact absent window included inside
    · intro zero window included inside
      exact (relation.mp ⟨window, included, inside⟩) zero


theorem segmented_hash_sequence [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List RoundRegion} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, WrappedProgramComputedProtocolWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval))
    (coverage : ProgramHashCallerCoverage data (first :: rest)) :
    SegmentedHashSequenceResult data before cells first rest := by
  exact ⟨program_hash_segmentation (by omega) clockInverse accepted inputs.toProtocolContextInputs
    inputs.registry scopes ordered coverage,
    wrapped_program_computed_protocol_sequence hp clockInverse accepted inputs scopes ordered⟩

end Airbender.UnifiedReduced.Caller.Proofs
