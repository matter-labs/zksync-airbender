import Airbender.Proofs.FullUnsigned.PublicRows
import Airbender.Proofs.Keccak.SplitInvocation

namespace Airbender.Delegation.Requests.Proofs
open Trace
set_option warningAsError true

/-- Exact virtual-token matching restricts to any full-width CSR subset. -/
theorem matching_csr_filter (selected : Nat → Bool) {calls fulfillments : List (Request p)}
    (matching : Matching calls fulfillments) :
    Matching (calls.filter (fun request => selected request.csr))
      (fulfillments.filter (fun request => selected request.csr)) := by
  let tokenSelected (token : MemoryToken p) :=
    selected (Nat.unpair (Nat.unpair token.address).2).1
  have filtered := matching.filter tokenSelected
  simpa [Matching, List.filter_map, Function.comp_def, tokenSelected,
    Request.issued, Request.empty, Request.token] using filtered

end Airbender.Delegation.Requests.Proofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
variable [Fact babyBearModulus.Prime]

/-- The combined request permutation supplies the exact split-worker channel. -/
theorem unrolled_full_split_request_matching
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus)
    (program : List Keccak.Split.Caller.ProgramEntry)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (families : ∀ row ∈ workers.rows, FullUnsigned.standardCall row.family) :
    let data : Keccak.Split.Native.RequestTrace babyBearModulus := ⟨trace, splitWorkers, program⟩
    Delegation.Requests.Matching data.calls data.fulfillments := by
  let selected (request : Delegation.Requests.Request babyBearModulus) :=
    (Keccak.Split.Caller.kindOfCSR request.csr).isSome
  have standard : (workers.rows.map Delegation.Requests.fulfillment).filter selected = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro request member
    obtain ⟨worker, present, rfl⟩ := List.mem_map.mp member
    have family := families worker present
    cases kind : worker.family <;>
      simp_all [FullUnsigned.standardCall, selected, Delegation.Requests.fulfillment,
        Delegation.Requests.csr, Keccak.Split.Caller.kindOfCSR]
  have split : (splitWorkers.rows.map
      (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)).filter selected =
        splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached) := by
    apply List.filter_eq_self.mpr
    intro request member
    obtain ⟨worker, present, rfl⟩ := List.mem_map.mp member
    cases worker with
    | mk kind assignment => cases kind <;> rfl
  have calls : (pooledCalls trace).filter selected =
      (Keccak.Split.Native.RequestTrace.mk trace splitWorkers program).calls := by
    simp [pooledCalls, Keccak.Split.Native.RequestTrace.calls,
      Keccak.Split.Native.RequestTrace.callers, List.filter_map,
      List.filter_filter, Function.comp_def, selected, Bool.and_assoc, Bool.and_comm]
  have matched := Delegation.Requests.Proofs.matching_csr_filter
    (fun csr => (Keccak.Split.Caller.kindOfCSR csr).isSome) accepted.requests
  change Delegation.Requests.Matching ((pooledCalls trace).filter selected)
    ((workers.rows.map Delegation.Requests.fulfillment ++ splitWorkers.rows.map
      (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)).filter selected) at matched
  rw [List.filter_append, standard, split, List.nil_append, calls] at matched
  exact matched

/-- A standard worker CSR cannot select one of the three split workers. -/
theorem unrolled_full_standard_not_split {w : Nat → ZMod babyBearModulus}
    {entry : Delegation.Caller.ProgramEntry}
    (family : FullUnsigned.standardCall entry.data.family)
    (query : Delegation.Caller.nativeQuery w = Delegation.Caller.query entry) :
    Keccak.Split.Caller.kindOfCSR (Delegation.Requests.caller w).csr = none := by
  have key := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[3]) query
  change w AddSub.importedConstraintsDecoderColumns.rs2 =
    (Delegation.Requests.csr entry.data.family : ZMod babyBearModulus) at key
  change Keccak.Split.Caller.kindOfCSR
    (w AddSub.importedConstraintsDecoderColumns.rs2).val = none
  rw [key, ZMod.val_natCast_of_lt]
  · cases kind : entry.data.family <;>
      simp_all [FullUnsigned.standardCall, Delegation.Requests.csr, Keccak.Split.Caller.kindOfCSR]
  · cases entry.data.family <;> decide

/-- Public decoder lookup and the combined permutation supply native split checks. -/
theorem unrolled_full_split_request_checks
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus)
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (families : ∀ row ∈ workers.rows, FullUnsigned.standardCall row.family)
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1) :
    Keccak.Split.Native.RequestChecks ⟨trace, splitWorkers,
      FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text⟩ := by
  refine {
    machineConstraints := accepted.cpuEquations
    machineActive := accepted.cpuActive
    states := accepted.states
    decoded := ?_
    workerEquations := equations
    workerActive := active
    requests := unrolled_full_split_request_matching splitWorkers _ accepted families }
  intro row member
  have present := (List.mem_filter.mp member).1
  have selected : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment ∧
      (Keccak.Split.Caller.kindOfCSR (Delegation.Requests.caller row.assignment).csr).isSome = true := by
    simpa only [Keccak.Split.Native.RequestTrace.callers, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, and_assoc] using (List.mem_filter.mp member).2
  rcases unrolled_full_native_row_classification setup lookup accepted excluded initialPC row present with
    ⟨_, _, _, _, _, ordinary⟩ | ⟨entry, included, _, _, query, _⟩ |
      ⟨entry, included, _, _, query, _⟩
  · exact False.elim (ordinary ⟨selected.1, selected.2.1⟩)
  · have fields := text_caller_sources FullUnsigned.standardDecoderFields initial text
      setup.image setup.size entry included
    have kind := (unrolled_full_caller_metadata fields.fields).2
    have absent := unrolled_full_standard_not_split kind query
    simp only [absent, Option.isSome_none] at selected
    exact False.elim (Bool.false_ne_true selected.2.2)
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp included
    exact ⟨i, query⟩

/-- The public full unsigned image supplies the split request input boundary. -/
theorem unrolled_full_split_request_inputs
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus}
    (splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus)
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (boundary : trace.initial = PCState.boundary 0 (4, 0)) :
    Keccak.Split.Native.RequestInputs
      ⟨trace, splitWorkers, FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text⟩
      initial ((FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text).map ProgramEntry.pc) := by
  refine ⟨unrolled_full_split_caller_image setup.image setup.size, ?_, ?_⟩
  · change (timeOfPair trace.initial.timestamp).Bounded
    rw [boundary]
    change 4 < timestampBase ∧ 0 < timestampBase
    decide
  · change (timeOfPair trace.initial.timestamp).value % 4 = 0
    rw [boundary]
    change 4 % 4 = 0
    decide

/-- Every split worker in the full native target has its actual public caller. -/
theorem unrolled_full_split_worker_callers
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus)
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (boundary : trace.initial = PCState.boundary 0 (4, 0))
    (families : ∀ row ∈ workers.rows, FullUnsigned.standardCall row.family)
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1) :
    let data : Keccak.Split.Native.RequestTrace babyBearModulus :=
      ⟨trace, splitWorkers, FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text⟩
    ∀ worker ∈ splitWorkers.rows, ∃ caller ∈ data.callers,
      worker.fulfillment splitWorkers.cached = Delegation.Requests.caller caller.assignment := by
  have initialPC : trace.initial.word.lo < limbBase := by
    rw [boundary]
    change 0 < limbBase
    decide
  have checked := unrolled_full_split_request_checks splitWorkers setup lookup accepted excluded
    initialPC families equations active
  have inputs := unrolled_full_split_request_inputs splitWorkers setup boundary
  dsimp only
  intro worker member
  exact Keccak.Split.Native.Proofs.native_worker_caller checked inputs member

end Airbender.Compiler.MachineTargets.Proofs
