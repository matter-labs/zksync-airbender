import Airbender.Review.Circuits.ReducedMachine.DecodedMain
import Airbender.Proofs.ReducedMachine.NativeUnifiedLocal
import Airbender.Proofs.ReducedMachine.NativeCSRPreservation
import Airbender.Proofs.ReducedMachine.NativeCallerDecoder
import Airbender.Proofs.ReducedMachine.NativeShiftRouting
import Airbender.Proofs.ReducedMachine.NativeArithmeticFields
import Airbender.Proofs.ReducedMachine.NativeBitwiseSelectors
import Airbender.Proofs.ReducedMachine.NativeComparisonSelectors
import Airbender.Proofs.ReducedMachine.NativeBranchSelectors
import Airbender.Proofs.ReducedMachine.NativeJumpSelectors
import Airbender.Proofs.ReducedMachine.NativeWordMemorySelectors
import Airbender.Proofs.ReducedMachine.NativeRuntimeQueries
import Airbender.Proofs.ReducedMachine.NativeRuntimeQueryTransport

namespace Airbender.NativeDecodedQueryDomainProofs
private abbrev F := ZMod mersenne31Modulus
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- All four actual tag equations, independent of table contents. -/
private theorem selector_formula {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    lookupSelectors w = #v[
      w 11 * w 22 + 17 * w 23 + 25 * w 24 + 17 * w 25 + 23 * w 27 + 47 * w 29 + 18 * w 31,
      w 11 * w 22 + 22 * w 23 + 24 * w 27 + 37 * w 29 + 23 * w 31,
      w 11 * w 22 + 37 * w 29, w 11 * w 22 + 20 * w 29] := by
  have e85 := assertion_of_holds holds ⟨85,by change 85 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e85
  have e89 := assertion_of_holds holds ⟨89,by change 89 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e89
  have e93 := assertion_of_holds holds ⟨93,by change 93 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e93
  have e97 := assertion_of_holds holds ⟨97,by change 97 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e97
  have a : w 103 = w 11 * w 22 + 17 * w 23 + 25 * w 24 + 17 * w 25 + 23 * w 27 + 47 * w 29 + 18 * w 31 := by linear_combination -e85
  have b : w 107 = w 11 * w 22 + 22 * w 23 + 24 * w 27 + 37 * w 29 + 23 * w 31 := by linear_combination -e89
  have c : w 111 = w 11 * w 22 + 37 * w 29 := by linear_combination -e93
  have d : w 115 = w 11 * w 22 + 20 * w 29 := by linear_combination -e97
  simp only [lookupSelectors,a,b,c,d]

private theorem vector_domain {v : Vector F 4} {values : Vector F 4}
    (same : v = values) (domain : ∀ slot : Fin 4, values[slot] ≠ 25) :
    ∀ slot : Fin 4, v[slot] ≠ 25 := by
  rw [same]
  exact domain

private theorem cast_domain (a : Nat) (bound : a < mersenne31Modulus) (other : a ≠ 25) :
    (a : F) ≠ 25 := by
  intro same
  have value := congrArg ZMod.val same
  rw [ZMod.val_natCast_of_lt bound] at value
  exact other value

private theorem constant_domain (a b c d : Nat)
    (ha : a < mersenne31Modulus) (hb : b < mersenne31Modulus)
    (hc : c < mersenne31Modulus) (hd : d < mersenne31Modulus)
    (na : a ≠ 25) (nb : b ≠ 25) (nc : c ≠ 25) (nd : d ≠ 25) :
    ∀ slot : Fin 4, (#v[(a : F),(b : F),(c : F),(d : F)])[slot] ≠ 25 := by
  intro slot
  fin_cases slot
  · exact cast_domain a ha na
  · exact cast_domain b hb nb
  · exact cast_domain c hc nc
  · exact cast_domain d hd nd

private theorem bitwise_tags {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (bitwiseMask useRegister : F)) :
    lookupSelectors w = #v[w 11,w 11,w 11,w 11] := by
  have equation := selector_formula holds
  have f22 := NativeBitwiseSelectorProofs.flags holds useRegister mask ⟨5,by decide⟩
  have f23 := NativeBitwiseSelectorProofs.flags holds useRegister mask ⟨6,by decide⟩
  have f24 := NativeBitwiseSelectorProofs.flags holds useRegister mask ⟨7,by decide⟩
  have f25 := NativeBitwiseSelectorProofs.flags holds useRegister mask ⟨8,by decide⟩
  have f27 := NativeBitwiseSelectorProofs.flags holds useRegister mask ⟨10,by decide⟩
  have f29 := NativeBitwiseSelectorProofs.flags holds useRegister mask ⟨12,by decide⟩
  have f31 := NativeBitwiseSelectorProofs.flags holds useRegister mask ⟨14,by decide⟩
  cases useRegister
  all_goals
    simp [NativeBitwiseSelectorProofs.bit] at f22 f23 f24 f25 f27 f29 f31
    simpa [f22,f23,f24,f25,f27,f29,f31] using equation

private theorem comparison_tags {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (useRegister : Bool) (mask : w 12 = (comparisonMask useRegister : F)) :
    lookupSelectors w = #v[17,22,0,0] := by
  have equation := selector_formula holds
  have f22 := NativeComparisonSelectorProofs.flags holds useRegister mask ⟨5,by decide⟩
  have f23 := NativeComparisonSelectorProofs.flags holds useRegister mask ⟨6,by decide⟩
  have f24 := NativeComparisonSelectorProofs.flags holds useRegister mask ⟨7,by decide⟩
  have f25 := NativeComparisonSelectorProofs.flags holds useRegister mask ⟨8,by decide⟩
  have f27 := NativeComparisonSelectorProofs.flags holds useRegister mask ⟨10,by decide⟩
  have f29 := NativeComparisonSelectorProofs.flags holds useRegister mask ⟨12,by decide⟩
  have f31 := NativeComparisonSelectorProofs.flags holds useRegister mask ⟨14,by decide⟩
  cases useRegister
  all_goals
    simp [NativeComparisonSelectorProofs.bit] at f22 f23 f24 f25 f27 f29 f31
    simpa [f22,f23,f24,f25,f27,f29,f31] using equation

private theorem branch_tags {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : F)) :
    lookupSelectors w = #v[17,22,0,0] := by
  have equation := selector_formula holds
  have f22 := NativeBranchSelectorProofs.flags holds mask ⟨5,by decide⟩
  have f23 := NativeBranchSelectorProofs.flags holds mask ⟨6,by decide⟩
  have f24 := NativeBranchSelectorProofs.flags holds mask ⟨7,by decide⟩
  have f25 := NativeBranchSelectorProofs.flags holds mask ⟨8,by decide⟩
  have f27 := NativeBranchSelectorProofs.flags holds mask ⟨10,by decide⟩
  have f29 := NativeBranchSelectorProofs.flags holds mask ⟨12,by decide⟩
  have f31 := NativeBranchSelectorProofs.flags holds mask ⟨14,by decide⟩
  simp [NativeBranchSelectorProofs.bit] at f22 f23 f24 f25 f27 f29 f31
  simpa [f22,f23,f24,f25,f27,f29,f31] using equation

private theorem jump_tags {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (jal : Bool) (mask : w 12 = (jumpMask jal : F)) :
    lookupSelectors w = #v[17,0,0,0] := by
  have equation := selector_formula holds
  have f22 := NativeJumpSelectorProofs.flags holds jal mask ⟨5,by decide⟩
  have f23 := NativeJumpSelectorProofs.flags holds jal mask ⟨6,by decide⟩
  have f24 := NativeJumpSelectorProofs.flags holds jal mask ⟨7,by decide⟩
  have f25 := NativeJumpSelectorProofs.flags holds jal mask ⟨8,by decide⟩
  have f27 := NativeJumpSelectorProofs.flags holds jal mask ⟨10,by decide⟩
  have f29 := NativeJumpSelectorProofs.flags holds jal mask ⟨12,by decide⟩
  have f31 := NativeJumpSelectorProofs.flags holds jal mask ⟨14,by decide⟩
  cases jal
  all_goals
    simp [NativeJumpSelectorProofs.bit] at f22 f23 f24 f25 f27 f29 f31
    simpa [f22,f23,f24,f25,f27,f29,f31] using equation

private theorem memory_tags {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : F)) :
    lookupSelectors w = #v[if store then 18 else 23,if store then 23 else 24,0,0] := by
  have equation := selector_formula holds
  have f22 := NativeWordMemorySelectorProofs.flags holds store mask ⟨5,by decide⟩
  have f23 := NativeWordMemorySelectorProofs.flags holds store mask ⟨6,by decide⟩
  have f24 := NativeWordMemorySelectorProofs.flags holds store mask ⟨7,by decide⟩
  have f25 := NativeWordMemorySelectorProofs.flags holds store mask ⟨8,by decide⟩
  have f27 := NativeWordMemorySelectorProofs.flags holds store mask ⟨10,by decide⟩
  have f29 := NativeWordMemorySelectorProofs.flags holds store mask ⟨12,by decide⟩
  have f31 := NativeWordMemorySelectorProofs.flags holds store mask ⟨14,by decide⟩
  cases store
  all_goals
    simp [NativeWordMemorySelectorProofs.bit] at f22 f23 f24 f25 f27 f29 f31
    simpa [f22,f23,f24,f25,f27,f29,f31] using equation

theorem supported {w : Nat → F} {entry : SupportedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    ∀ slot : Fin 4, (lookupSelectors w)[slot] ≠ 25 := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with shift | arithmetic | bitwise | comparison | branch | jump
  · obtain ⟨selected,_,_,_,source,same⟩ := shift
    obtain ⟨useRegister,mask⟩ := (NativeShiftDecoderProofs.decoded_fields source (query.trans same.symm)).mask
    exact vector_domain (NativeShiftRoutingProofs.tags holds selected.data.family useRegister mask)
      (constant_domain 47 37 37 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · obtain ⟨selected,_,_,_,source,same⟩ := arithmetic
    exact vector_domain (NativeArithmeticFieldProofs.tags holds selected.data.family
      (NativeArithmeticDecoderProofs.decoded_fields source (query.trans same.symm)).mask)
      (constant_domain 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · obtain ⟨selected,_,_,_,source,same⟩ := bitwise
    have decoded := NativeBitwiseDecoderProofs.decoded_fields source (query.trans same.symm)
    apply vector_domain (bitwise_tags holds selected.data.family.useRegister decoded.mask)
    rw [decoded.funct3]
    cases selected.data.family.kind <;> exact constant_domain _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨selected,_,_,_,source,same⟩ := comparison
    exact vector_domain (comparison_tags holds selected.data.family.useRegister
      (NativeComparisonDecoderProofs.decoded_fields source (query.trans same.symm)).mask)
      (constant_domain 17 22 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · obtain ⟨selected,_,_,_,source,same⟩ := branch
    exact vector_domain (branch_tags holds (NativeBranchDecoderProofs.decoded_fields source (query.trans same.symm)).mask)
      (constant_domain 17 22 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · obtain ⟨selected,_,_,_,source,same⟩ := jump
    exact vector_domain (jump_tags holds selected.data.family (NativeJumpDecoderProofs.decoded_fields source (query.trans same.symm)).mask)
      (constant_domain 17 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

theorem unified {w : Nat → F} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    ∀ slot : Fin 4, (lookupSelectors w)[slot] ≠ 25 := by
  rcases NativeUnifiedDecoderProofs.entry_profile fields with ordinary | memory
  · obtain ⟨selected,_,_,_,source,_,same⟩ := ordinary
    exact supported holds source (query.trans same.symm)
  · obtain ⟨selected,_,_,_,source,_,same⟩ := memory
    have tags := memory_tags holds selected.data.family
      (NativeWordMemoryDecoderProofs.decoded_fields source (query.trans same.symm)).mask
    apply vector_domain tags
    cases selected.data.family
    · exact constant_domain 23 24 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact constant_domain 18 23 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Both constant queries and all four dynamic queries retain the SAME data. -/
theorem fixed_queries {w : Nat → F} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    NativeFixed.table.Contains #[] #v[w 36,w 56,w 57,16] ∧
    NativeFixed.table.Contains #[] #v[w 48,w 59,w 60,16] ∧
    ∀ slot : Fin 4, NativeFixed.table.Contains #[]
      #v[w (100 + 4 * slot.val),w (101 + 4 * slot.val),w (102 + 4 * slot.val),w (103 + 4 * slot.val)] := by
  have constants := NativeRuntimeQueryProofs.queries holds
  refine ⟨Airbender.NativeRuntimeQueryTransportProofs.outside_csr _ constants.1 (by change (16 : F) ≠ 25; decide +kernel),
    Airbender.NativeRuntimeQueryTransportProofs.outside_csr _ constants.2 (by change (16 : F) ≠ 25; decide +kernel),?_⟩
  intro slot
  apply Airbender.NativeRuntimeQueryTransportProofs.outside_csr _ (NativeRuntimeQueryProofs.dynamic_queries holds slot)
  have domain := unified holds fields query slot
  fin_cases slot <;> simpa [lookupSelectors] using domain

/-- Abstract source/target assembly keeps every assertion and all22 queries.
    Only the six actual fixed-table queries require new membership derivations. -/
private theorem assemble {source target : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints source))
    (first : target.Contains #[] #v[w 36,w 56,w 57,16])
    (second : target.Contains #[] #v[w 48,w 59,w 60,16])
    (dynamic : ∀ slot : Fin 4, target.Contains #[]
      #v[w (100 + 4 * slot.val),w (101 + 4 * slot.val),w (102 + 4 * slot.val),w (103 + 4 * slot.val)]) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints target) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · exact (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).1
  · intro lookup member
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    change Fin 22 at i
    fin_cases i
    · exact lookup_of_holds holds ⟨0,by change 0 < 22; decide⟩
    · exact lookup_of_holds holds ⟨1,by change 1 < 22; decide⟩
    · exact lookup_of_holds holds ⟨2,by change 2 < 22; decide⟩
    · exact lookup_of_holds holds ⟨3,by change 3 < 22; decide⟩
    · exact lookup_of_holds holds ⟨4,by change 4 < 22; decide⟩
    · exact lookup_of_holds holds ⟨5,by change 5 < 22; decide⟩
    · exact lookup_of_holds holds ⟨6,by change 6 < 22; decide⟩
    · exact lookup_of_holds holds ⟨7,by change 7 < 22; decide⟩
    · exact lookup_of_holds holds ⟨8,by change 8 < 22; decide⟩
    · exact lookup_of_holds holds ⟨9,by change 9 < 22; decide⟩
    · exact lookup_of_holds holds ⟨10,by change 10 < 22; decide⟩
    · exact lookup_of_holds holds ⟨11,by change 11 < 22; decide⟩
    · exact lookup_of_holds holds ⟨12,by change 12 < 22; decide⟩
    · exact lookup_of_holds holds ⟨13,by change 13 < 22; decide⟩
    · exact lookup_of_holds holds ⟨14,by change 14 < 22; decide⟩
    · exact lookup_of_holds holds ⟨15,by change 15 < 22; decide⟩
    · simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,
        Table.toRaw,Expression.eval,environment,ProvableType.fromElements] using first
    · simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,
        Table.toRaw,Expression.eval,environment,ProvableType.fromElements] using second
    · simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,
        Table.toRaw,Expression.eval,environment,ProvableType.fromElements] using dynamic 0
    · simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,
        Table.toRaw,Expression.eval,environment,ProvableType.fromElements] using dynamic 1
    · simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,
        Table.toRaw,Expression.eval,environment,ProvableType.fromElements] using dynamic 2
    · simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,
        Table.toRaw,Expression.eval,environment,ProvableType.fromElements] using dynamic 3

/-- Complete BODY is derived only after actual public-decoded query domains. -/
theorem fixed_body {w : Nat → F} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table) := by
  have actual := fixed_queries holds fields query
  exact assemble holds actual.1 actual.2.1 actual.2.2

/-- Original ordinary7-or-CSR public projection derives the actual main write
    rule on RuntimePool. The CSR branch uses its unchanged generic table proof. -/
theorem main_write_rule (row : Row mersenne31Modulus NativeReducedFamily)
    {entry : Airbender.NativeCallerDecoder.Program}
    (holds : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (fields : Airbender.NativeCallerDecoder.decoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) (aligned : row.start.word.lo % 4 = 0) :
    Airbender.Trace.Proofs.RowWriteBoundsFromReads row := by
  rcases Airbender.NativeCallerDecoderProofs.entry_profile fields with ordinary | csr
  · obtain ⟨selected,_,source,same⟩ := ordinary
    have actualQuery := query.trans same.symm
    exact NativeUnifiedLocalProofs.row_write_rule row (fixed_body holds source actualQuery) source actualQuery aligned
  · obtain ⟨selected,_,source,same⟩ := csr
    exact NativeCSRPreservationProofs.row_write_rule row holds source (query.trans same.symm)

/-- Actual membership in the original stateful public image supplies the entry,
    all ten fields and the query domain; no per-row mask or query is assumed. -/
theorem public_body {w : Nat → F} {setup : SparseDecoderSetup UnifiedMode}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (∀ slot : Fin 4, (lookupSelectors w)[slot] ≠ 25) ∧
      FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table) := by
  obtain ⟨entry,_,source,query⟩ := NativeUnifiedDecoderProofs.fetched_sources image holds member
  exact ⟨unified holds source.fields query,fixed_body holds source.fields query⟩

/-- Reuse original public PC reconstruction and sparse-image alignment before
    the local write rule. Every actual active main position is covered. -/
theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (config : Airbender.Blake2Worker.Native.WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : Airbender.Blake2Worker.Native.WorkerBatch Setup R}
    {inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary}
    {inverse : Airbender.ReducedMachine.NativeMemoryBoundary.BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch) :
    Airbender.NativeDecodedMain.Effects batch := by
  have sources := Airbender.NativeMainDecoderProofs.public_sources publicSetup embed memory ch pc gamma decoder config accepted image lookups
  intro proof member i ordinary active
  obtain ⟨entry,present,source,query⟩ := sources proof member i ordinary active
  have canonical := Airbender.Trace.Proofs.native_query_pc_word (by decide : Arithmetic.limbBase < mersenne31Modulus) query
  change initialPCWord (proof.initialization.main.memory.rows i) = Arithmetic.Word.ofBitVec entry.pc at canonical
  have aligned : (initialPCWord (proof.initialization.main.memory.rows i)).lo % 4 = 0 := by
    rw [canonical]
    exact (Airbender.Trace.Proofs.run_sparse_setup_sources image present).2
  exact main_write_rule _ (accepted.access proof member i ordinary).body source.fields query aligned

end Airbender.NativeDecodedQueryDomainProofs
