import Airbender.Proofs.Reduced.PublicCallers

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Public setup and native selectors classify every actual reduced machine row. -/
theorem reduced_native_row_classification
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → ProgramRows.Mask} {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .reduced initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers [] [])
    (families : ∀ row ∈ trace.rows, AddSub.Modular.External.Caller.reducedFamily row.family = true)
    (initialPC : trace.initial.word.lo < limbBase) :
    ∀ row ∈ trace.rows,
      (∃ entry ∈ ProgramRows.programOf .reduced initial text,
        entry.SourceWith initial AddSub.Modular.External.decoderFields ∧
          entry.data.family = row.family ∧ row.decoderQuery = entry.query ∧
          ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment)) ∨
      (∃ entry ∈ FullUnsigned.entriesWith reducedCallerFields text,
        entry.SourceWith initial Delegation.Caller.decoderFields ∧
          row.family = .addSub ∧
          Delegation.Caller.nativeQuery row.assignment = Delegation.Caller.query entry ∧
          Delegation.Requests.Selected row.assignment) := by
  intro row member
  have typed := reduced_native_query_pc_low accepted initialPC row member
  have classified := unrolled_native_row_case setup lookup row member typed
  rcases classified with ⟨entry, included, source, family, masked⟩ | ⟨caller, included, source, family, masked⟩
  · have fullSource : entry.SourceWith initial AddSub.Modular.External.decoderFields :=
      ⟨source.bytes, source.decoded, AddSub.Modular.External.Caller.Proofs.reduced_fields_original source.fields⟩
    have omitted (which : row.family = .addSub ∨ row.family = .wordMemory) : row.decoderQuery[7] = entry.query[7] := by
      have funct3Zero := stream_dropped_funct3 fullSource (by rwa [family])
      have native : row.decoderQuery[7] = 0 := by
        cases row with
        | mk kind w => rcases which with rfl | rfl <;> rfl
      simpa [ProgramEntry.query, funct3Zero] using native
    have query := reduced_mask_query row.family (families row member) (masks row.family)
      (setup.maskMatches row.family) omitted masked
    refine Or.inl ⟨entry, included, fullSource, family, query, ?_⟩
    rintro ⟨selectedFamily, selected⟩
    have properties := stream_addsub_properties fullSource (family.trans selectedFamily)
    cases row with
    | mk kind w =>
      cases selectedFamily
      have holds := accepted.cpuEquations ⟨.addSub, w⟩ member
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have packed := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[8]) query
      have flag := addsub_packed_selector (by decide) core entry.data.mask properties.2.1 packed 7
      have zero : w AddSub.importedConstraintsDecoderColumns.flags[7] = 0 := by
        change w AddSub.importedConstraintsDecoderColumns.flags[7] =
          (if entry.data.mask.testBit 7 then 1 else 0) at flag
        rw [properties.2.2] at flag
        exact flag
      exact zero_ne_one (zero.symm.trans selected)
  · have omitted (_which : row.family = .addSub ∨ row.family = .wordMemory) : row.decoderQuery[7] = caller.query[7] := by
      cases row with
      | mk kind w => cases family; rfl
    have query := reduced_mask_query row.family (families row member) (masks row.family)
      (setup.maskMatches row.family) omitted masked
    obtain ⟨entry, present, original, _, _, converted⟩ := reduced_public_caller initial text setup.image setup.size caller included
    refine Or.inr ⟨entry, present, original, family, ?_, ?_⟩
    · cases row with
      | mk kind w => cases family; exact query.trans converted
    · cases row with
      | mk kind w =>
        cases family
        have holds := accepted.cpuEquations ⟨.addSub, w⟩ member
        have core := Verification.holds_of_sublist holds
          (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
        have packed := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[8]) query
        exact addsub_packed_selector (by decide) core 128 (by decide) packed 7

/-- Exact public decoder lookup supplies the reduced shared native acceptance. -/
theorem reduced_native_acceptance {initial : State} {text : List (BitVec 32)}
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle)
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .reduced initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers [] [])
    (families : ∀ row ∈ trace.rows, AddSub.Modular.External.Caller.reducedFamily row.family = true)
    (initialPC : trace.initial.word.lo < limbBase) :
    Delegation.Caller.MixedMemoryAccepted ⟨trace, workers, (reducedProgram initial text bundles).callers⟩
      (reducedProgram initial text bundles).ordinary := by
  have classified := reduced_native_row_classification setup lookup accepted families initialPC
  refine {
    constraints := accepted.cpuEquations
    active := accepted.cpuActive
    states := accepted.states
    decoded := ?_
    workerConstraints := accepted.workerEquations
    workerActive := accepted.workerActive
    requests := by simpa only [pooledCalls, Delegation.Caller.RequestTrace.calls,
      Delegation.Caller.RequestTrace.callers, Delegation.Caller.RequestTrace.fulfillments,
      List.append_nil] using accepted.requests
    ordinaryDecoded := ?_
    memory := by simpa only [pooledSteps, Delegation.Caller.RequestTrace.mixedSteps,
      List.append_nil] using accepted.ram }
  · intro row member
    have selected := (List.mem_filter.mp member).2
    have choice : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by simpa using selected
    rcases classified row (List.mem_filter.mp member).1 with ordinary | caller
    · obtain ⟨_, _, _, _, _, excluded⟩ := ordinary
      exact False.elim (excluded choice)
    · obtain ⟨entry, included, _, _, query, _⟩ := caller
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp included
      exact ⟨i, query⟩
  · intro row member ordinary
    rcases classified row member with standard | caller
    · obtain ⟨entry, included, _, family, query, _⟩ := standard
      have filtered : entry ∈ ((reducedProgram initial text bundles).ordinary.filter
          fun candidate => candidate.data.family == row.family) :=
        List.mem_filter.mpr ⟨included, by simpa using family⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp filtered
      exact ⟨i, query⟩
    · obtain ⟨_, _, _, family, _, selected⟩ := caller
      apply False.elim
      apply ordinary
      exact List.mem_filter.mpr ⟨member, by simp [family, selected]⟩

end Airbender.Compiler.MachineTargets.Proofs
