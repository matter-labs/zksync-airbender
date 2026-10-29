import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.MemoryExecuteNative.UnifiedUncached

namespace Airbender.Compiler.FramedWitnessNative.UnifiedUncached
open Airbender Airbender.Compiler
open Airbender.Compiler.MaterializedWitnessNative.UnifiedUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem framed_graph_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedUncached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      RowWitness hom challenges gamma sourceValue counts row baseValue values ∧
      ∀ address, addressEqual (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.placement address)) address = false →
        baseValue address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback address := by
  let initial := Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback)
  let values := Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical hom challenges gamma baseValue
  have sourceArithmetic := Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.full_arithmetic_extends extended holds
  have arithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.gates sourceArithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bankRoundTrip extended full sourceArithmetic.1
      (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback) wire
  have externalAgreement (address) (outside) :
      baseValue address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback address :=
    WireBank.materialize_external Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank full (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback) address outside
  have baseLaw := Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_base hom challenges gamma baseValue
  have affine := Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_affines hom challenges gamma baseValue arithmetic
  have lookups := Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_lookups hom challenges gamma baseValue
  have products := Airbender.Compiler.FunctionalNative.UnifiedUncached.native.canonical_products hom challenges gamma baseValue
  have countsAt (index) : baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.get index)) = counts index := by
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.counts_at initial counts index)
  have setupAt := Airbender.Compiler.OracleFrameNative.UnifiedUncached.native.materialized_cells Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row fallback full
  have helpers : ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedUncached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.sourceValues baseValue)).val < 524288 := by
    intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement Airbender.Compiler.HelperNative.UnifiedUncached.native.placement
      Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.helper_membership sourceValue primitives field member
  have outputs : OutputsPreserved hom challenges gamma sourceValue counts row values := by
    let assignment : TypedAssignment R := ⟨baseValue, values⟩
    have typedEq : assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom baseLaw
    have defined : ∀ definition ∈ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) := by
      rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.lookupDefinitionsAgree]
      exact affine
    have helperDefined : ∀ definition ∈ Airbender.Compiler.HelperNative.UnifiedUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) := by
      rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.helperDefinitionsAgree]
      exact affine
    have holds : ∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedUncached.native.gates, gate.Holds hom challenges gamma (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) := by
      rw [typedEq]
      exact lookups
    unfold OutputsPreserved
    refine ⟨?_ , ?_ , ?_⟩
    · have tableCells : ∀ column ∈ Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns, assignment.base column.address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.value row column := by
        intro column member
        exact setupAt column (of_decide_eq_true (List.all_eq_true.mp genericColumns column member))
      have countCell : assignment.base (.BaseLayerWitness 57) = counts ⟨0, by decide⟩ := countsAt ⟨0, by decide⟩
      have reduced := Airbender.Compiler.TableNative.UnifiedUncached.native.genericSourceTableReduction hom challenges gamma assignment defined
        (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.lookupCopies baseValue arithmetic) holds (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.value row) (counts ⟨0, by decide⟩) tableCells countCell
      rw [typedEq] at reduced
      apply reduced.trans
      congr 2
      apply List.map_congr_left
      intro query member
      apply Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.queries_preserved hom challenges.lookupAlpha gamma sourceValue counts baseValue inputAgreement query
      simp only [Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.queries, List.mem_append]
      exact Or.inl member
    · have tableCells : ∀ column ∈ Airbender.Compiler.TableNative.UnifiedUncached.native.range16SetupColumns, assignment.base column.address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.value row column := by
        intro column member
        exact setupAt column (of_decide_eq_true (List.all_eq_true.mp range16Columns column member))
      have countCell : assignment.base (.BaseLayerWitness 55) = counts ⟨1, by decide⟩ := countsAt ⟨1, by decide⟩
      have reduced := Airbender.Compiler.TableNative.UnifiedUncached.native.range16SourceTableReduction hom challenges gamma assignment defined
        (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.lookupCopies baseValue arithmetic) holds (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.value row) (counts ⟨1, by decide⟩) tableCells countCell
      rw [typedEq] at reduced
      apply reduced.trans
      congr 2
      apply List.map_congr_left
      intro query member
      apply Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.queries_preserved hom challenges.lookupAlpha gamma sourceValue counts baseValue inputAgreement query
      simp only [Airbender.Compiler.QueryFrameNative.UnifiedUncached.native.queries, List.mem_append]
      exact Or.inr member
    · have tableCells : ∀ column ∈ Airbender.Compiler.TableNative.UnifiedUncached.native.timestampSetupColumns, assignment.base column.address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.value row column := by
        intro column member
        exact setupAt column (of_decide_eq_true (List.all_eq_true.mp timestampColumns column member))
      have countCell : assignment.base (.BaseLayerWitness 56) = counts ⟨2, by decide⟩ := countsAt ⟨2, by decide⟩
      have reduced := Airbender.Compiler.HelperNative.UnifiedUncached.native.timestampSourceReduction hom challenges gamma assignment helperDefined
        (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.helperCopies baseValue arithmetic) holds
      change (Airbender.Compiler.LookupNative.UnifiedUncached.native.timestampOutput).value (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) =
        (Airbender.Compiler.HelperNative.UnifiedUncached.native.fields.map (fun field => RationalPair.leaf 1 (hom (field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.sourceValues baseValue)) + gamma)) ++
          [NativeLookupLeaf.registryValue Airbender.Compiler.LookupNative.UnifiedUncached.native.registry hom challenges gamma (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) 13]).sum at reduced
      rw [Airbender.Compiler.TableNative.UnifiedUncached.native.timestampSetupInterpreted hom challenges gamma assignment defined
        (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.value row) (counts ⟨2, by decide⟩) tableCells countCell, typedEq] at reduced
      apply reduced.trans
      congr 2
      apply List.map_congr_left
      intro field member
      have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement Airbender.Compiler.HelperNative.UnifiedUncached.native.placement
        Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.transportChecked field member)
        (Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.canonical sourceValue) counts) baseValue inputAgreement
      change field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.sourceValues baseValue) = _ at same
      rw [same, Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.helpers_preserved (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.canonical sourceValue) counts field member]
  refine ⟨baseValue, values, ?_, externalAgreement⟩
  exact ⟨inputAgreement, arithmetic, baseLaw, affine, lookups, products, countsAt, setupAt, helpers, outputs⟩

def MemoryOutputsPreserved {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (sourceValue : Fin 137 → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) (values : GKRAddress → R) : Prop :=
  values (GKRAddress.InnerLayer 4 8) = (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod
  ∧ values (GKRAddress.InnerLayer 4 9) = (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod
  ∧ values (GKRAddress.InnerLayer 4 6) = maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback))) ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod)
  ∧ values (GKRAddress.InnerLayer 4 7) = maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback))) ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod)

theorem memory_outputs_preserved {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField)
    (baseValue : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (witness : RowWitness hom challenges gamma sourceValue counts row baseValue values)
    (externalAgreement : ∀ address, addressEqual (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.placement address)) address = false →
      baseValue address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback address) :
    MemoryOutputsPreserved hom challenges sourceValue fallback values := by
  rcases witness with ⟨inputAgreement, arithmetic, baseLaw, affine, _, products, _, _, _, _⟩
  let assignment : TypedAssignment R := ⟨baseValue, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.UnifiedUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  unfold MemoryOutputsPreserved
  refine ⟨?_ , ?_ , ?_ , ?_⟩
  · have reduced := Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadSourceReduction hom challenges assignment defined
      (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryCopies baseValue arithmetic) holds
    rw [typedEq] at reduced
    apply reduced.trans
    change (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues baseValue) hom challenges)).prod = (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod
    apply congrArg List.prod
    apply List.map_congr_left
    intro entry member
    apply Source.MemoryRow.fingerprint_congr
    intro field included
    apply Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.initialization_fields_preserved Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row sourceValue counts fallback baseValue inputAgreement externalAgreement field
    change field ∈ (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows ++ Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows).flatMap Source.MemoryRow.fields
    exact List.mem_flatMap.mpr ⟨entry, List.mem_append_left _ member, included⟩
  · have reduced := Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteSourceReduction hom challenges assignment defined
      (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryCopies baseValue arithmetic) holds
    rw [typedEq] at reduced
    apply reduced.trans
    change (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues baseValue) hom challenges)).prod = (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod
    apply congrArg List.prod
    apply List.map_congr_left
    intro entry member
    apply Source.MemoryRow.fingerprint_congr
    intro field included
    apply Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.initialization_fields_preserved Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row sourceValue counts fallback baseValue inputAgreement externalAgreement field
    change field ∈ (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows ++ Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows).flatMap Source.MemoryRow.fields
    exact List.mem_flatMap.mpr ⟨entry, List.mem_append_right _ member, included⟩
  · have reduced := Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadSourceReduction hom challenges assignment defined
      (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryCopies baseValue arithmetic) holds
    rw [typedEq] at reduced
    apply reduced.trans
    change maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues baseValue))) ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues baseValue) hom challenges)).prod) = _
    have executeSame := Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.execute_fields_preserved Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row sourceValue counts fallback baseValue
      inputAgreement externalAgreement Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute (by simp [Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.executeFields])
    rw [executeSame]
    by_cases inactive : Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) = 0
    · simp only [inactive, map_zero, maskProduct_inactive]
    · have active : Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue) ≠ 0 := by
        rw [← Airbender.Compiler.MemoryExecuteNative.UnifiedUncached.native.execute_source sourceValue fallback]
        exact inactive
      apply congrArg (maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback))))
      apply congrArg List.prod
      apply List.map_congr_left
      intro entry member
      apply Source.MemoryRow.fingerprint_congr
      intro field included
      apply Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.ram_fields_preserved Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row sourceValue counts fallback baseValue inputAgreement externalAgreement active field
      change field ∈ (Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows).flatMap Source.MemoryRow.fields
      exact List.mem_flatMap.mpr ⟨entry, List.mem_append_left _ member, included⟩
  · have reduced := Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteSourceReduction hom challenges assignment defined
      (Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native.memoryCopies baseValue arithmetic) holds
    rw [typedEq] at reduced
    apply reduced.trans
    change maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues baseValue))) ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues baseValue) hom challenges)).prod) = _
    have executeSame := Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.execute_fields_preserved Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row sourceValue counts fallback baseValue
      inputAgreement externalAgreement Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute (by simp [Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.executeFields])
    rw [executeSame]
    by_cases inactive : Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback) = 0
    · simp only [inactive, map_zero, maskProduct_inactive]
    · have active : Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue) ≠ 0 := by
        rw [← Airbender.Compiler.MemoryExecuteNative.UnifiedUncached.native.execute_source sourceValue fallback]
        exact inactive
      apply congrArg (maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues sourceValue fallback))))
      apply congrArg List.prod
      apply List.map_congr_left
      intro entry member
      apply Source.MemoryRow.fingerprint_congr
      intro field included
      apply Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.ram_fields_preserved Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model row sourceValue counts fallback baseValue inputAgreement externalAgreement active field
      change field ∈ (Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows).flatMap Source.MemoryRow.fields
      exact List.mem_flatMap.mpr ⟨entry, List.mem_append_right _ member, included⟩

theorem complete_row_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedUncached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedUncached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      RowWitness hom challenges gamma sourceValue counts row baseValue values ∧
      (∀ address, addressEqual (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.placement address)) address = false →
        baseValue address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback address) ∧
      MemoryOutputsPreserved hom challenges sourceValue fallback values := by
  obtain ⟨baseValue, values, witness, externalAgreement⟩ :=
    framed_graph_extends hom challenges gamma sourceValue original clockValid primitives counts row fallback
  exact ⟨baseValue, values, witness, externalAgreement,
    memory_outputs_preserved hom challenges gamma sourceValue counts row fallback baseValue values witness externalAgreement⟩

def CompleteRowWitness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField)
    (baseValue : GKRAddress → Source.BaseField) (values : GKRAddress → R) : Prop :=
  RowWitness hom challenges gamma sourceValue counts row baseValue values ∧
  (∀ address, addressEqual (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.placement address)) address = false →
    baseValue address = Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.baseOracle row fallback address) ∧
  MemoryOutputsPreserved hom challenges sourceValue fallback values

theorem complete_trace_extends
    (sourceValue : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → Fin 137 → Source.BaseField)
    (original : ∀ row, Satisfies (Airbender.Compiler.SourceContractNative.UnifiedUncached.native.originals.map Expression.polynomial) (sourceValue row))
    (clockValid : ∀ row, Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedUncached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project (sourceValue row)))
    (primitives : ∀ row, Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project (sourceValue row)))
      (Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement.memory.project (sourceValue row)))
    (authored : ∀ row, AuthoredLookupValid (sourceValue row))
    (fallback : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → GKRAddress → Source.BaseField) :
    ∃ counts : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → Fin 3 → Source.BaseField,
      ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R),
      ∃ baseValue : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → GKRAddress → Source.BaseField,
      ∃ values : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → GKRAddress → R,
        (∀ row, CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)) ∧
        ∀ group : Fin 3, ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map
          (fun row => (outputPorts group).value (values row))).sum.numerator = 0 := by
  obtain ⟨counts, cancel⟩ := Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.grouped_trace_counter_witness setupColumns Airbender.Compiler.MaterializedNative.UnifiedUncached.native.positive
    (fun row => sourceRequests (sourceValue row))
    (fun row => source_requests_valid (sourceValue row) (primitives row) (authored row))
  refine ⟨counts, ?_⟩
  intro R _ hom challenges gamma
  classical
  have complete (row : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length) :
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) baseValue values :=
    complete_row_extends hom challenges gamma (sourceValue row) (original row) (clockValid row)
      (primitives row) (counts row) row (fallback row)
  choose baseValue values correct using complete
  refine ⟨baseValue, values, correct, ?_⟩
  intro group
  have same : ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => (outputPorts group).value (values row))) =
      ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row =>
        (((sourceRequests (sourceValue row) group).map (fun query => query.value hom challenges.lookupAlpha gamma)) ++
          [(Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.row (setupColumns group) row (counts row group)).value hom challenges.lookupAlpha gamma]).sum)) := by
    apply List.map_congr_left
    intro row _
    exact outputs_preserved_uniform hom challenges gamma (sourceValue row) (counts row) row (values row)
      (correct row).1.2.2.2.2.2.2.2.2.2 group
  rw [same]
  exact cancel group hom challenges.lookupAlpha gamma

theorem memory_trace_products_preserved {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → Fin 137 → Source.BaseField)
    (counts : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → Fin Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns.length → Source.BaseField)
    (fallback : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → GKRAddress → Source.BaseField)
    (baseValue : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → GKRAddress → Source.BaseField)
    (values : Fin Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length → GKRAddress → R)
    (witnesses : ∀ row, CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row
      (fallback row) (baseValue row) (values row)) :
  ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => values row (GKRAddress.InnerLayer 4 8))).prod =
    ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues (sourceValue row) (fallback row)) hom challenges)).prod)).prod
  ∧ ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => values row (GKRAddress.InnerLayer 4 9))).prod =
    ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => (Airbender.Compiler.MemoryNative.UnifiedUncached.native.initializationWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues (sourceValue row) (fallback row)) hom challenges)).prod)).prod
  ∧ ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => values row (GKRAddress.InnerLayer 4 6))).prod =
    ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues (sourceValue row) (fallback row)))) ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues (sourceValue row) (fallback row)) hom challenges)).prod))).prod
  ∧ ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => values row (GKRAddress.InnerLayer 4 7))).prod =
    ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.imported.data.length).map (fun row => maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues (sourceValue row) (fallback row)))) ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.memoryWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedUncached.native.sourceMemoryValues (sourceValue row) (fallback row)) hom challenges)).prod))).prod := by
  refine ⟨?_ , ?_ , ?_ , ?_⟩
  · apply congrArg List.prod
    apply List.map_congr_left
    intro row _
    exact (witnesses row).2.2.1
  · apply congrArg List.prod
    apply List.map_congr_left
    intro row _
    exact (witnesses row).2.2.2.1
  · apply congrArg List.prod
    apply List.map_congr_left
    intro row _
    exact (witnesses row).2.2.2.2.1
  · apply congrArg List.prod
    apply List.map_congr_left
    intro row _
    exact (witnesses row).2.2.2.2.2

end Airbender.Compiler.FramedWitnessNative.UnifiedUncached
