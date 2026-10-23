import Airbender.Review.Trace.UnifiedReduced.Paths.SpanExecution
import Airbender.Proofs.UnifiedReduced.PathSpans
import Airbender.Proofs.UnifiedReduced.PathExecution
import Airbender.Proofs.UnifiedReduced.PathSpanAlgorithms

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Every aligned syntactic caller occurrence has exactly one actual worker. -/
theorem path_protocol_worker_unique [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (call : PathProtocolOccurrence data) :
    ∃! worker, worker ∈ data.workers.windowRows call.start (call.start + 4) := by
  obtain ⟨_, window⟩ := path_caller_window hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization call.code (by have := call.aligned; omega)
  have count : (data.workers.windowRows call.start (call.start + 4)).length = 1 := by
    have same : (call.start + 4) - 4 = call.start := by omega
    rw [same] at window
    rw [← window.workerCount, window.machineCount]
    omega
  have nonempty : data.workers.windowRows call.start (call.start + 4) ≠ [] := by
    intro empty
    rw [empty] at count
    simp at count
  obtain ⟨worker, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  refine ⟨worker, member, ?_⟩
  intro other included
  have singleton : data.workers.windowRows call.start (call.start + 4) = [worker] := by
    cases same : data.workers.windowRows call.start (call.start + 4) with
    | nil => simp [same] at member
    | cons first rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa [same] using count)
      subst rest
      have equal : worker = first := by simpa only [same, List.mem_singleton] using member
      simp only [equal]
  simpa only [singleton, List.mem_singleton] using included

/-- The worker family and invocation are derived from the actual occurrence. -/
theorem path_protocol_worker_facts [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (call : PathProtocolOccurrence data) {worker : Delegation.Row p}
    (member : worker ∈ data.workers.windowRows call.start (call.start + 4)) :
    worker.family = call.family ∧
      (timeOfPair (Delegation.Requests.fulfillment worker).time).value = call.start + 1 := by
  obtain ⟨_, window⟩ := path_caller_window hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization call.code (by have := call.aligned; omega)
  have family := window.family worker (by simpa using member)
  obtain ⟨caller, matched, _⟩ := window.requests.workerMatches worker (by simpa using member)
  have nativeMember := List.mem_of_mem_filter (List.mem_of_mem_filter matched.1)
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clocks := machine_clock_facts (by norm_num [timestampBase]; omega) inverse
    accepted.toRequestChecks inputs.publicProgram nativeMember
  have aligned := call.aligned
  have clock := clocks.1
  have invocation := matched.2.2.invocation
  change (timeOfPair (Delegation.Requests.fulfillment worker).time).value =
    Delegation.Caller.startClock caller + 1 at invocation
  exact ⟨family, by omega⟩

/-- Current native participation covers every worker by one public protocol
    occurrence; no all-issued or desired worker-partition premise is supplied. -/
theorem path_protocol_worker_covered
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {bigints : List (PathBigintOccurrence data)}
    {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ data.workers.rows) :
    ∃ call ∈ pathProtocolOccurrences bigints spans,
      worker ∈ data.workers.windowRows call.start (call.start + 4) := by
  have requests := request_binding (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
  have native := ExternalBoundary.Requests.Proofs.native_binding accepted.toRequestChecks requests
  obtain ⟨caller, called, matched, slot⟩ := ExternalBoundary.Requests.Proofs.covered requests native worker member
  have decoded := accepted.decoded caller called
  change ∃ i : Fin data.program.length, caller.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let entry := data.program.get i
  have pcWord : caller.start.word = Word.ofBitVec entry.pc := caller_query_pc_word (by decide) query
  have pc : entry.pc = caller.start.word.toBitVec := by rw [pcWord, Word.ofBitVec_roundtrip]
  obtain ⟨call, included, start, _⟩ := inputs.coverage caller (List.mem_of_mem_filter called)
    entry (List.get_mem _ _) pc
  have write := slot.writes (path_native_control_port worker.family) (path_control_port_member worker)
  have normalized : worker.writeTime =
      (timeOfPair (worker.writeToken (path_native_control_port worker.family)).time).value := by
    cases worker with
    | mk family w => cases family <;> rfl
  refine ⟨call, included, List.mem_filter.mpr ⟨member, decide_eq_true ?_⟩⟩
  rw [normalized, write, ← start]
  omega

/-- Exact full-pool occurrence bijection and list multiplicity. Every protocol
    index is realized, and native participation leaves no surplus worker. -/
theorem path_protocol_partition
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {bigints : List (PathBigintOccurrence data)}
    {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans) :
    PathProtocolPartition (pathProtocolOccurrences bigints spans) := by
  classical
  let calls := pathProtocolOccurrences bigints spans
  let rows : Fin calls.length → Delegation.Row babyBearModulus :=
    fun i => Classical.choose (path_protocol_worker_unique (by decide) (by decide) accepted
      inputs.toProtocolContextInputs (calls.get i))
  have members (i : Fin calls.length) :
      rows i ∈ data.workers.windowRows (calls.get i).start ((calls.get i).start + 4) :=
    (Classical.choose_spec (path_protocol_worker_unique (by decide) (by decide) accepted
      inputs.toProtocolContextInputs (calls.get i))).1
  have facts (i : Fin calls.length) := path_protocol_worker_facts (by decide) (by decide) accepted
    inputs.toProtocolContextInputs (calls.get i) (members i)
  have startsInjective : Function.Injective (fun i : Fin calls.length => (calls.get i).start) := by
    intro i j same
    have equal : (calls.map PathProtocolOccurrence.start).get ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩ =
        (calls.map PathProtocolOccurrence.start).get ⟨j.val, by simp only [List.length_map]; exact j.isLt⟩ := by
      simpa only [List.get_eq_getElem, List.getElem_map] using same
    have indices := inputs.distinctOccurrences.injective_get equal
    apply Fin.ext
    exact congrArg (fun index : Fin (calls.map PathProtocolOccurrence.start).length => index.val) indices
  have injective : Function.Injective rows := by
    intro i j same
    have first := (facts i).2
    have second := (facts j).2
    rw [same] at first
    apply startsInjective
    change (calls.get i).start = (calls.get j).start
    omega
  have requests := request_binding (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
  have liveFilter : data.fulfillments.filter (fun request => decide (Delegation.Requests.Live request)) =
      data.fulfillments := by
    apply List.filter_eq_self.mpr
    intro request included
    obtain ⟨worker, member, rfl⟩ := List.mem_map.mp included
    exact decide_eq_true (Delegation.Proofs.active_invocation_live
      (accepted.workerConstraints worker member) (accepted.workerActive worker member))
  have keys : (data.workers.rows.map fun worker => (Delegation.Requests.fulfillment worker).time).Nodup := by
    have invocations := requests.invocations.2
    rw [liveFilter] at invocations
    simpa only [RequestTrace.fulfillments, List.map_map, Function.comp_def] using invocations
  have nativeUnique : data.workers.rows.Nodup := keys.of_map _
  have iffMembership : ∀ worker, worker ∈ List.ofFn rows ↔ worker ∈ data.workers.rows := by
    intro worker
    constructor
    · intro included
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp included
      exact List.mem_of_mem_filter (members i)
    · intro member
      obtain ⟨call, included, inside⟩ := path_protocol_worker_covered accepted inputs member
      obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp included
      let i : Fin calls.length := ⟨index, bound⟩
      have selected : calls.get i = call := equal
      have same := (Classical.choose_spec (path_protocol_worker_unique (by decide) (by decide) accepted
        inputs.toProtocolContextInputs (calls.get i))).2 worker (by simpa only [selected] using inside)
      exact List.mem_ofFn.mpr ⟨i, same.symm⟩
  refine ⟨rows, injective, ?_, ?_⟩
  · intro i
    exact ⟨members i, (facts i).1, (facts i).2⟩
  · exact (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr injective) nativeUnique).mpr iffMembership

/-- Complete protocol counts account for the entire native worker list. -/
theorem path_protocol_count
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {bigints : List (PathBigintOccurrence data)}
    {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans) :
    data.workers.rows.length = bigints.length + (spans.map fun span => span.span.callCount).sum := by
  obtain ⟨rows, _, _, permutation⟩ := path_protocol_partition accepted inputs
  have count := permutation.length_eq
  simp only [List.length_ofFn] at count
  have lengths : ∀ chain : List (PathCompleteSpan data program),
      (chain.flatMap fun span => List.ofFn span.occurrence).length =
        (chain.map fun span => span.span.callCount).sum := by
    intro chain
    induction chain with
    | nil => rfl
    | cons span rest ih => simp only [List.flatMap_cons, List.length_append, List.length_ofFn,
        List.map_cons, List.sum_cons, ih]
  simpa only [pathProtocolOccurrences, List.length_append, List.length_map, lengths spans] using count.symm


/-- Complete protocol syntax constructs a local plan at every position. G's
    first actual index0 seeds arbitrary pointers; later calls use public frames. -/
def path_span_call_plan [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program)
    (i : Fin span.span.callCount) : PathCallPlan data program := by
  rcases span with ⟨family, start, increasing, aligned, code, control, gFrames⟩
  cases family with
  | blakeG reduced =>
    refine ⟨start i, .hash ⟨.blakeG reduced, i⟩, code i, control i, ?_⟩
    change PathGPointerPreparation data program (start i)
    right
    let first := PathCompleteSpan.first (.blakeG reduced)
    have seedControl : PathControllerDataflow data program (start first) 12
        (Blake2G.controlAt reduced 0).toBitVec := control first
    by_cases zero : i.val = 0
    · have same : i = first := Fin.ext zero
      rw [same]
      exact .atSeed reduced (code first) seedControl
    · have frames := gFrames rfl i (by omega)
      exact .afterSeed reduced (code first) seedControl frames.1 frames.2
  | blakeRound flags => exact ⟨start i, .hash ⟨.blakeRound flags, i⟩, code i, control i, trivial⟩
  | keccak => exact ⟨start i, .hash ⟨.keccak, i⟩, code i, control i, trivial⟩

theorem path_span_call_plan_start [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program)
    (i : Fin span.span.callCount) : (path_span_call_plan span i).start = span.start i := by
  rcases span with ⟨family, start, increasing, aligned, code, control, frames⟩
  cases family <;> rfl

theorem path_span_call_plan_family [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program)
    (i : Fin span.span.callCount) : (path_span_call_plan span i).position.family = span.span.family := by
  rcases span with ⟨family, start, increasing, aligned, code, control, frames⟩
  cases family <;> rfl

def path_span_call_plans [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program) :
    List (PathCallPlan data program) := List.ofFn (path_span_call_plan span)

def path_bigint_call_plan [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (call : PathBigintOccurrence data) : PathCallPlan data program :=
  ⟨call.start, .bigint, call.code, trivial, trivial⟩

def path_spans_call_plans [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (bigints : List (PathBigintOccurrence data))
    (spans : List (PathCompleteSpan data program)) : List (PathCallPlan data program) :=
  bigints.map path_bigint_call_plan ++ spans.flatMap path_span_call_plans

/-- Plan construction preserves every occurrence start, family and multiplicity. -/
theorem path_spans_call_plan_metadata [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (bigints : List (PathBigintOccurrence data))
    (spans : List (PathCompleteSpan data program)) :
    (path_spans_call_plans bigints spans).map (fun plan => (plan.start, plan.position.family)) =
      (pathProtocolOccurrences bigints spans).map (fun call => (call.start, call.family)) := by
  have spanMetadata (span : PathCompleteSpan data program) :
      (path_span_call_plans span).map (fun plan => (plan.start, plan.position.family)) =
        (List.ofFn span.occurrence).map (fun call => (call.start, call.family)) := by
    simp only [path_span_call_plans, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact Prod.ext (path_span_call_plan_start span i) (path_span_call_plan_family span i)
  simp only [path_spans_call_plans, pathProtocolOccurrences, List.map_append, List.map_map,
    List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro span _
  exact spanMetadata span

/-- Complete public spans construct the broader local-call input contract.
    Pointer separation, masks, requests and calls remain proof outputs. -/
def path_spans_call_inputs [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {bigints : List (PathBigintOccurrence data)}
    {spans : List (PathCompleteSpan data program)}
    (inputs : PathSpansInputs data initial ca oa cells program bigints spans) :
    PathCallsInputs data initial ca oa cells program (path_spans_call_plans bigints spans) := by
  have metadata := path_spans_call_plan_metadata bigints spans
  refine { toProtocolContextInputs := inputs.toProtocolContextInputs, distinctPlans := ?_, coverage := ?_ }
  · have starts := congrArg (List.map Prod.fst) metadata
    simp only [List.map_map, Function.comp_def] at starts
    rw [starts]
    exact inputs.distinctOccurrences
  · intro row member entry included pc
    obtain ⟨call, present, start, family⟩ := inputs.coverage row member entry included pc
    have pairMember : (call.start, call.family) ∈
        (path_spans_call_plans bigints spans).map (fun plan => (plan.start, plan.position.family)) := by
      rw [metadata]
      exact List.mem_map.mpr ⟨call, present, rfl⟩
    obtain ⟨plan, planned, pair⟩ := List.mem_map.mp pairMember
    exact ⟨plan, planned, (congrArg Prod.fst pair).trans start, (congrArg Prod.snd pair).trans family⟩

/-- Complete spans and bigint calls realize the whole actual mixed path. -/
theorem path_spans_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) :
    Realizes (FullStep program data.program) data.machine initial cells :=
  path_execution accepted (path_spans_call_inputs inputs) profile pc commands

/-- Every span chooses its own syntactic noninterference certificate. One
    internally derived native history supplies whole execution and all grouped
    algorithms, including mixed arbitrary-seed readonly and computed-store spans. -/
theorem path_spans_result_with_gap_certificates [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (gaps : ∀ span ∈ spans, PathSpanGapCertificate span) :
    PathSpansResult data program initial cells bigints spans := by
  have calls := path_spans_call_inputs inputs
  have memory := path_calls_memory_inputs (by decide) (by decide) accepted calls
  have effects := mixed_memory_effects accepted memory
  have ledger := ExternalBoundary.Requests.Proofs.native_binding accepted.toRequestChecks effects.requests
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  have execution := full_execution_at accepted memory profile.code effects.requests pc ledger permutation order history
    (fun _ member ordinary => ordinary_cycle_at accepted memory profile effects permutation order history member ordinary)
    (fun _ member => path_full_caller_cycle_at accepted calls profile.code commands effects permutation order history member)
    terminal
  refine ⟨execution, path_protocol_partition accepted inputs, path_protocol_count accepted inputs,
    events, finalState, permutation, order, history, ?_⟩
  intro span present
  rcases gaps span present with readonly | computed
  · exact path_span_algorithm_at accepted memory span readonly order history permutation
  · rcases computed with ⟨certificate⟩
    exact path_span_algorithm_at_computed_stores accepted memory span certificate order history permutation

/-- Whole execution and all readonly-gap algorithms share one derived native
    history. Ordinary link/register/RAM effects and terminal PC/cells remain. -/
theorem path_spans_result [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (gaps : ∀ span ∈ spans, PathSpanReadOnlyGaps span) :
    PathSpansResult data program initial cells bigints spans :=
  path_spans_result_with_gap_certificates accepted inputs profile pc commands
    (fun span present => Or.inl (gaps span present))

/-- Computed-disjoint stores use the same derived history and shared algorithm
    body; their actual writes remain in whole execution and the gap histories. -/
theorem path_spans_result_computed_stores [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (gaps : ∀ span ∈ spans, PathSpanComputedStoreGaps span) :
    PathSpansResult data program initial cells bigints spans :=
  path_spans_result_with_gap_certificates accepted inputs profile pc commands
    (fun span present => Or.inr ⟨gaps span present⟩)

end Airbender.UnifiedReduced.Caller.Proofs
