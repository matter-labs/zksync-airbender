import Airbender.Review.Trace.UnifiedReduced.Paths.Spans
import Airbender.Proofs.UnifiedReduced.PathGPointerSeed
import Mathlib.Data.List.FinRange

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

private theorem path_span_singleton {α : Type*} {rows : List α} {row : α}
    (count : rows.length = 1) (member : row ∈ rows) : rows = [row] := by
  cases rows with
  | nil => simp at member
  | cons first rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using count)
    subst rest
    have same : row = first := by simpa using member
    subst first
    rfl

/-- Public code at one indexed occurrence derives exactly one actual worker. -/
theorem path_span_worker_unique [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) (i : Fin span.span.callCount) :
    ∃! worker, worker ∈ data.workers.windowRows (span.start i) (span.start i + 4) := by
  obtain ⟨floor, window⟩ := path_caller_window hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization (span.code i) (by have := span.aligned i; omega)
  have count : (data.workers.windowRows (span.start i) (span.start i + 4)).length = 1 := by
    have same : (span.start i + 4) - 4 = span.start i := by omega
    rw [same] at window
    rw [← window.workerCount, window.machineCount]
    omega
  have nonempty : data.workers.windowRows (span.start i) (span.start i + 4) ≠ [] := by
    intro empty
    rw [empty] at count
    simp at count
  obtain ⟨worker, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  refine ⟨worker, member, ?_⟩
  intro other included
  have singleton := path_span_singleton count member
  simpa only [singleton, List.mem_singleton] using included

/-- The native invocation is the actual indexed caller start plus one. -/
theorem path_span_worker_time [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) (i : Fin span.span.callCount)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.windowRows (span.start i) (span.start i + 4)) :
    (timeOfPair (Delegation.Requests.fulfillment worker).time).value = span.start i + 1 := by
  obtain ⟨_, window⟩ := path_caller_window hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization (span.code i) (by have := span.aligned i; omega)
  obtain ⟨caller, matched, _⟩ := window.requests.workerMatches worker (by simpa using member)
  have nativeMember := List.mem_of_mem_filter (List.mem_of_mem_filter matched.1)
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clocks := machine_clock_facts (by norm_num [timestampBase]; omega) inverse
    accepted.toRequestChecks inputs.publicProgram nativeMember
  have aligned := span.aligned i
  have clock := clocks.1
  have invocation := matched.2.2.invocation
  change (timeOfPair (Delegation.Requests.fulfillment worker).time).value =
    Delegation.Caller.startClock caller + 1 at invocation
  omega

/-- The controller binding at every index follows from actual raw matching
    and public computation, before masks or architectural history. -/
theorem path_span_worker_binding [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) (i : Fin span.span.callCount)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.windowRows (span.start i) (span.start i + 4)) :
    HashCallPosition.NativeBinding ⟨span.span, i⟩ worker := by
  obtain ⟨_, window⟩ := path_caller_window hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization (span.code i) (by have := span.aligned i; omega)
  have family := window.family worker (by simpa using member)
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  have nonzero : span.span.controlRegister ≠ 0 := by
    cases span.span with
    | blakeG reduced => change (12 : BitVec 5) ≠ 0; decide
    | blakeRound flags => change (12 : BitVec 5) ≠ 0; decide
    | keccak => change (10 : BitVec 5) ≠ 0; decide
  have raw := path_caller_control_read hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization unique (span.code i) (by have := span.aligned i; omega)
    (value := (HashCallPosition.word ⟨span.span, i⟩).toBitVec)
    (by
      intro tokens matching
      have seed := path_controller_dataflow_token hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
        inputs.initialization unique inputs.tables (span.control i) nonzero (span.aligned i) (by simpa using matching)
      simpa only [path_hash_control_register] using seed)
    (by simpa using member)
  have read := raw.trans (path_hash_word_canonical ⟨span.span, i⟩)
  refine ⟨family, ?_⟩
  rcases span with ⟨protocol, start, increasing, aligned, code, control, frames⟩
  cases protocol <;> simpa only [family, path_native_control_port, Delegation.Caller.HashSpan.family] using read

/-- Every indexed worker exists exactly once in the selected native bucket.
    Strict public clock order gives an injective actual worker map; native
    invocation uniqueness retains exact list multiplicity. -/
theorem path_complete_span_actual [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) : span.Actual := by
  classical
  let rows : Fin span.span.callCount → Delegation.Row p :=
    fun i => Classical.choose (path_span_worker_unique hp inverse accepted inputs span i)
  have members (i : Fin span.span.callCount) :
      rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4) :=
    (Classical.choose_spec (path_span_worker_unique hp inverse accepted inputs span i)).1
  have times (i : Fin span.span.callCount) :
      (timeOfPair (Delegation.Requests.fulfillment (rows i)).time).value = span.start i + 1 :=
    path_span_worker_time hp inverse accepted inputs span i (members i)
  have injective : Function.Injective rows := by
    intro i j same
    have first := times i
    have second := times j
    rw [same] at first
    exact span.increasing.injective (by omega)
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size inverse accepted.toRequestChecks inputs.publicProgram
  let selected := fun worker : Delegation.Row p => decide (∃ i : Fin span.span.callCount,
    (timeOfPair (Delegation.Requests.fulfillment worker).time).value = span.start i + 1)
  have live : ∀ worker ∈ data.workers.rows, selected worker = true →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) := by
    intro worker _ included zero
    obtain ⟨i, time⟩ := of_decide_eq_true included
    rw [zero] at time
    have floor := path_controller_dataflow_after_initial (span.control i)
    norm_num [timeOfPair, Timestamp.value] at time
  let issued := data.workers.rows.filter fun worker => decide (Delegation.Requests.Live (Delegation.Requests.fulfillment worker))
  have issuedKeys : (issued.map fun worker => (Delegation.Requests.fulfillment worker).time).Nodup := by
    simpa only [issued, RequestTrace.fulfillments, List.filter_map, List.map_map, Function.comp_def]
      using requests.invocations.2
  have equalFilter : span.nativeRows = issued.filter selected := by
    dsimp only [PathCompleteSpan.nativeRows, issued]
    rw [List.filter_filter]
    apply List.filter_congr
    intro worker member
    change selected worker = (selected worker && decide (Delegation.Requests.Live (Delegation.Requests.fulfillment worker)))
    by_cases inside : selected worker = true
    · have active := live worker member inside
      rw [inside, decide_eq_true active]
      rfl
    · have absent : selected worker = false := Bool.eq_false_iff.mpr inside
      rw [absent]
      rfl
  have nativeUnique : span.nativeRows.Nodup := by
    rw [equalFilter]
    exact (issuedKeys.of_map _).filter _
  have iffMembership : ∀ worker, worker ∈ List.ofFn rows ↔ worker ∈ span.nativeRows := by
    intro worker
    constructor
    · intro included
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp included
      exact List.mem_filter.mpr ⟨List.mem_of_mem_filter (members i),
        decide_eq_true ⟨i, times i⟩⟩
    · intro included
      obtain ⟨member, selected⟩ := List.mem_filter.mp included
      obtain ⟨i, time⟩ := of_decide_eq_true selected
      have write := Delegation.Caller.Proofs.worker_write_time (by omega)
        (requests.clocks worker member).1 (requests.clocks worker member).2
      have inside : worker ∈ data.workers.windowRows (span.start i) (span.start i + 4) := by
        apply List.mem_filter.mpr
        refine ⟨member, decide_eq_true ?_⟩
        rw [write]
        omega
      have same := (Classical.choose_spec (path_span_worker_unique hp inverse accepted inputs span i)).2 worker inside
      exact List.mem_ofFn.mpr ⟨i, same.symm⟩
  refine ⟨rows, injective, ?_, ?_⟩
  · intro i
    exact ⟨members i, path_span_worker_binding hp inverse accepted inputs span i (members i)⟩
  · exact (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr injective) nativeUnique).mpr iffMembership

/-- The complete native span has the pinned full protocol count. -/
theorem path_complete_span_count [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) : span.nativeRows.length = span.span.callCount := by
  obtain ⟨rows, _, _, permutation⟩ := path_complete_span_actual hp inverse accepted inputs span
  simpa only [List.length_ofFn] using permutation.length_eq.symm

end Airbender.UnifiedReduced.Caller.Proofs
