import Airbender.Proofs.UnifiedReduced.StreamPublicCallers

namespace Airbender.Compiler.MachineTargets.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail NativeDecoder
open UnifiedReduced
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
variable [Fact babyBearModulus.Prime]

/-- State matching bounds incoming decoder PCs without a CPU-only RAM premise. -/
theorem unified_native_query_pc_low {trace : UnifiedTrace babyBearModulus}
    {workers : Delegation.MemoryData babyBearModulus}
    (accepted : UnifiedAcceptance trace workers)
    (initial : trace.initial.word.lo < limbBase) :
    ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536 := by
  have outputs (row : Row babyBearModulus UnifiedFamily) (member : row ∈ trace.rows) :
      row.finish.word.lo < limbBase := by
    have holds := accepted.cpuEquations row member
    cases row with
    | mk family w =>
      cases family
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
      exact (UnifiedReduced.Proofs.pc_bounds core).1
  intro row member
  have present : row.start ∈ trace.initial :: trace.rows.map Row.finish :=
    accepted.states.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  have bound : row.start.word.lo < limbBase := by
    rcases List.mem_cons.mp present with same | written
    · simpa only [same] using initial
    · obtain ⟨previous, included, same⟩ := List.mem_map.mp written
      simpa only [same] using outputs previous included
  cases row with
  | mk family w => cases family; exact bound

/-- Public setup and native flags classify each actual unified row completely. -/
theorem unified_native_row_classification
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List (ZMod babyBearModulus))}
    {trace : UnifiedTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (lookup : UnifiedDecoderExactLookup trace mask columns)
    (accepted : UnifiedAcceptance trace workers)
    (initialPC : trace.initial.word.lo < limbBase) :
    ∀ row ∈ trace.rows,
      (∃ entry ∈ UnifiedProgramRows.ordinaryProgramOf initial text,
        entry.SourceWith initial Caller.Stream.decoderFields ∧ row.decoderQuery = entry.query ∧
          ¬ Caller.Selected row.assignment) ∨
      (∃ entry ∈ FullUnsigned.entriesWith Delegation.Caller.decoderFields text,
        entry.SourceWith initial Delegation.Caller.decoderFields ∧
          row.decoderQuery = Delegation.Caller.query entry ∧ Caller.Selected row.assignment) := by
  intro row member
  have typed := unified_native_query_pc_low accepted initialPC row member
  have classified := unified_native_row_case setup lookup row member typed
  have core := Verification.holds_of_sublist (accepted.cpuEquations row member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  rcases classified with ⟨entry, included, source, masked⟩ | ⟨caller, included, source, masked⟩
  · have query := unified_mask_query mask setup.maskMatches masked
    have fields := source.fields
    rw [unified_decoder_fields] at fields
    refine Or.inl ⟨entry, included, ⟨source.bytes, source.decoded, fields⟩, query, ?_⟩
    cases row with
    | mk family w =>
      cases family
      have flag := UnifiedReduced.Proofs.decoder_selectors (by decide) core
        (Caller.Stream.Proofs.field_bounds fields).2.1 query 7
      have zero := Caller.Stream.Proofs.stream_caller_disabled fields
      have disabled : w importedConstraintsDecoderColumns.flags[7] = 0 := by simpa [zero] using flag
      intro selected
      exact zero_ne_one (disabled.symm.trans selected)
  · have query := unified_mask_query mask setup.maskMatches masked
    obtain ⟨entry, present, source, _, _, converted⟩ :=
      unified_public_caller initial text setup.image setup.size caller included
    refine Or.inr ⟨entry, present, source, query.trans converted, ?_⟩
    cases row with
    | mk family w =>
      cases family
      have packed := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[8]) query
      have selectors := Caller.Stream.Proofs.selector_of_packed_query (by decide) core
        128 (by decide) packed 7
      exact selectors

/-- Public decoder lookup supplies the native combined acceptance relation. -/
theorem unified_native_acceptance
    {initial : State} {text : List (BitVec 32)}
    (bundles : List Caller.DelegationUse.Bundle)
    {capacity : Nat} {mask : ProgramRows.Mask} {columns : List (List (ZMod babyBearModulus))}
    {trace : UnifiedTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (lookup : UnifiedDecoderExactLookup trace mask columns)
    (accepted : UnifiedAcceptance trace workers)
    (initialPC : trace.initial.word.lo < limbBase) :
    Caller.MixedMemoryAccepted ⟨trace, workers, (unifiedProgram initial text bundles).callers⟩
      (unifiedProgram initial text bundles).ordinary := by
  let data : Caller.RequestTrace babyBearModulus := ⟨trace, workers, (unifiedProgram initial text bundles).callers⟩
  have classified := unified_native_row_classification setup lookup accepted initialPC
  refine {
    constraints := accepted.cpuEquations
    active := accepted.cpuActive
    states := accepted.states
    decoded := ?_
    workerConstraints := accepted.workerEquations
    workerActive := accepted.workerActive
    requests := accepted.requests
    ordinaryDecoded := ?_
    memory := accepted.ram }
  · intro row member
    have selected : Caller.Selected row.assignment := of_decide_eq_true (List.mem_filter.mp member).2
    rcases classified row (List.mem_filter.mp member).1 with ordinary | caller
    · obtain ⟨_, _, _, _, excluded⟩ := ordinary
      exact False.elim (excluded selected)
    · obtain ⟨entry, included, _, query, _⟩ := caller
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp included
      exact ⟨i, query⟩
  · intro row member ordinary
    rcases classified row member with standard | caller
    · obtain ⟨entry, included, _, query, _⟩ := standard
      have filtered : entry ∈ ((unifiedProgram initial text bundles).ordinary.filter
          fun entry => entry.data.family == UnifiedFamily.machine) :=
        List.mem_filter.mpr ⟨included, by cases entry.data.family; rfl⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp filtered
      exact ⟨i, query⟩
    · obtain ⟨_, _, _, _, selected⟩ := caller
      exact False.elim (ordinary (List.mem_filter.mpr ⟨member, decide_eq_true selected⟩))

end Airbender.Compiler.MachineTargets.Proofs
