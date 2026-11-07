import Airbender.Proofs.FullUnsigned.PublicCallers

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Exact public lookup classifies all six native families and both caller pools. -/
theorem unrolled_full_native_row_classification
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → ProgramRows.Mask} {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase) :
    ∀ row ∈ trace.rows,
      (∃ entry ∈ ProgramRows.programOf .fullUnsigned initial text,
        entry.SourceWith initial AddSub.Modular.External.decoderFields ∧
          entry.data.family = row.family ∧ row.decoderQuery = entry.query ∧
          ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment)) ∨
      (∃ entry ∈ FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text,
        entry.SourceWith initial Delegation.Caller.decoderFields ∧
          row.family = .addSub ∧
          Delegation.Caller.nativeQuery row.assignment = Delegation.Caller.query entry ∧
          Delegation.Requests.Selected row.assignment) ∨
      (∃ entry ∈ FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text,
        entry.SourceWith initial Keccak.Split.Caller.decoderFields ∧
          row.family = .addSub ∧
          Delegation.Caller.nativeQuery row.assignment = Keccak.Split.Caller.query entry ∧
          Delegation.Requests.Selected row.assignment) := by
  intro row member
  have typed := unrolled_full_native_query_pc_low accepted initialPC row member
  have classified := unrolled_native_row_case setup lookup row member typed
  rcases classified with ⟨entry, included, source, family, masked⟩ | ⟨caller, included, source, family, masked⟩
  · have fullSource : entry.SourceWith initial AddSub.Modular.External.decoderFields := source
    have omitted (which : row.family = .addSub ∨ row.family = .wordMemory ∨
        row.family = .mulDiv ∨ row.family = .subwordMemory) : row.decoderQuery[7] = entry.query[7] := by
      have funct3Zero := unrolled_full_dropped_funct3 fullSource (by rwa [family])
      have native : row.decoderQuery[7] = 0 := by
        cases row with
        | mk kind w => rcases which with rfl | rfl | rfl | rfl <;> rfl
      simpa [ProgramEntry.query, funct3Zero] using native
    have query := unrolled_full_mask_query row.family (masks row.family)
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
  · have omitted (_which : row.family = .addSub ∨ row.family = .wordMemory ∨
        row.family = .mulDiv ∨ row.family = .subwordMemory) : row.decoderQuery[7] = caller.query[7] := by
      cases row with
      | mk kind w => cases family; rfl
    have query := unrolled_full_mask_query row.family (masks row.family)
      (setup.maskMatches row.family) omitted masked
    have selected : Delegation.Requests.Selected row.assignment := by
      cases row with
      | mk kind w =>
        cases family
        have holds := accepted.cpuEquations ⟨.addSub, w⟩ member
        have core := Verification.holds_of_sublist holds
          (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
        have packed := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[8]) query
        exact addsub_packed_selector (by decide) core 128 (by decide) packed 7
    rcases unrolled_full_public_caller initial text setup.image setup.size excluded caller included with
      ⟨entry, present, original, _, _, converted⟩ | ⟨entry, present, original, _, _, converted⟩
    · refine Or.inr (Or.inl ⟨entry, present, original, family, ?_, selected⟩)
      cases row with
      | mk kind w => cases family; exact query.trans converted
    · refine Or.inr (Or.inr ⟨entry, present, original, family, ?_, selected⟩)
      cases row with
      | mk kind w => cases family; exact query.trans converted

end Airbender.Compiler.MachineTargets.Proofs
