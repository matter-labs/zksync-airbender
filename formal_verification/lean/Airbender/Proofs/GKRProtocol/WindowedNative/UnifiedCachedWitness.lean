import Airbender.Proofs.GKRProtocol.WindowedNative.UnifiedCachedTokens
import Airbender.Proofs.GKRProtocol.WindowedNative.UnifiedCachedAgreement
import Airbender.Proofs.GKRProtocol.CleanWitnessNative.UnifiedCached

namespace Airbender.Compiler.WindowedNative.UnifiedCached
open Airbender Airbender.Compiler
open Airbender.Compiler.MaterializedWitnessNative.UnifiedCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def ActualRowWitness (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (counts : Fin 3 → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (baseValue : GKRAddress → Source.BaseField)
    (values : GKRAddress → R) : Prop :=
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.WindowedNative.UnifiedCached.productGates publicTops, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ Airbender.Compiler.OracleFrameNative.UnifiedCached.native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)).val < 524288) ∧
      OutputsPreserved hom challenges gamma sourceValue counts row values

theorem graph_extends (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 137 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      ActualRowWitness publicTops hom challenges gamma sourceValue counts row baseValue values ∧
      values = Airbender.Compiler.WindowedNative.UnifiedCached.canonical publicTops hom challenges gamma baseValue ∧
      ∀ address, addressEqual (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.placement address)) address = false →
        baseValue address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback address := by
  let initial := Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue
  let extended := Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned initial counts
  have holds := Airbender.Compiler.CounterFrameNative.UnifiedCached.native.source_preserved initial counts (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.source_holds sourceValue original clockValid)
  let full := Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.translation.extend extended
  let baseValue := Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.materialize full (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback)
  let values := Airbender.Compiler.WindowedNative.UnifiedCached.canonical publicTops hom challenges gamma baseValue
  have sourceArithmetic := Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.full_arithmetic_extends extended holds
  have arithmetic := WireBank.materialize_gates Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bankRoundTrip full
    (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback) Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates sourceArithmetic.2
  have inputAgreement (wire) : baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = extended wire :=
    WireBank.materialize_source_input Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.projection
      Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bankRoundTrip extended full sourceArithmetic.1
      (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback) wire
  have externalAgreement (address) (outside) :
      baseValue address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback address :=
    WireBank.materialize_external Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank full (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback) address outside
  have baseLaw := Airbender.Compiler.WindowedNative.UnifiedCached.canonical_base publicTops hom challenges gamma baseValue
  have affine := Airbender.Compiler.WindowedNative.UnifiedCached.canonical_affines publicTops hom challenges gamma baseValue arithmetic
  have lookups := Airbender.Compiler.WindowedNative.UnifiedCached.canonical_lookups publicTops hom challenges gamma baseValue
  have products := Airbender.Compiler.WindowedNative.UnifiedCached.canonical_products publicTops hom challenges gamma baseValue
  have countsAt (index) : baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.get index)) = counts index := by
    have actual := inputAgreement (Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots index)
    rw [Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slotsRoundTrip index] at actual
    exact actual.trans (Airbender.Compiler.CounterFrameNative.UnifiedCached.native.counts_at initial counts index)
  have setupAt := Airbender.Compiler.OracleFrameNative.UnifiedCached.native.materialized_cells Airbender.Compiler.MaterializedNative.UnifiedCached.native.model row fallback full
  have helpers : ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)).val < 524288 := by
    intro field member
    have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement Airbender.Compiler.HelperNative.UnifiedCached.native.placement
      Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.UnifiedCached.native.transportChecked field member)
      extended baseValue inputAgreement
    change (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.placement.project (baseValue ∘ Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.address))).val < 524288
    rw [same, Airbender.Compiler.CounterFrameNative.UnifiedCached.native.helpers_preserved initial counts field member]
    exact Airbender.Compiler.HelperValidityNative.UnifiedCached.native.helper_membership sourceValue primitives field member
  have outputs : OutputsPreserved hom challenges gamma sourceValue counts row values := by
    let assignment : TypedAssignment R := ⟨baseValue, values⟩
    have typedEq : assignment.value Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing hom baseLaw
    have defined : ∀ definition ∈ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing hom) := by
      rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupDefinitionsAgree]
      exact affine
    have helperDefined : ∀ definition ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing hom) := by
      rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperDefinitionsAgree]
      exact affine
    have holds : ∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma (assignment.value Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing hom) := by
      rw [typedEq]
      exact lookups
    unfold OutputsPreserved
    refine ⟨?_ , ?_ , ?_⟩
    · have tableCells : ∀ column ∈ Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns, assignment.base column.address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row column := by
        intro column member
        exact setupAt column (of_decide_eq_true (List.all_eq_true.mp genericColumns column member))
      have countCell : assignment.base (.BaseLayerWitness 57) = counts ⟨0, by decide⟩ := countsAt ⟨0, by decide⟩
      have reduced := Airbender.Compiler.TableNative.UnifiedCached.native.genericSourceTableReduction hom challenges gamma assignment defined
        (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies baseValue arithmetic) holds (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row) (counts ⟨0, by decide⟩) tableCells countCell
      rw [typedEq] at reduced
      apply reduced.trans
      congr 2
      apply List.map_congr_left
      intro query member
      apply Airbender.Compiler.QueryFrameNative.UnifiedCached.native.queries_preserved hom challenges.lookupAlpha gamma sourceValue counts baseValue inputAgreement query
      simp only [Airbender.Compiler.QueryFrameNative.UnifiedCached.native.queries, List.mem_append]
      exact Or.inl member
    · have tableCells : ∀ column ∈ Airbender.Compiler.TableNative.UnifiedCached.native.range16SetupColumns, assignment.base column.address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row column := by
        intro column member
        exact setupAt column (of_decide_eq_true (List.all_eq_true.mp range16Columns column member))
      have countCell : assignment.base (.BaseLayerWitness 55) = counts ⟨1, by decide⟩ := countsAt ⟨1, by decide⟩
      have reduced := Airbender.Compiler.TableNative.UnifiedCached.native.range16SourceTableReduction hom challenges gamma assignment defined
        (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.lookupCopies baseValue arithmetic) holds (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row) (counts ⟨1, by decide⟩) tableCells countCell
      rw [typedEq] at reduced
      apply reduced.trans
      congr 2
      apply List.map_congr_left
      intro query member
      apply Airbender.Compiler.QueryFrameNative.UnifiedCached.native.queries_preserved hom challenges.lookupAlpha gamma sourceValue counts baseValue inputAgreement query
      simp only [Airbender.Compiler.QueryFrameNative.UnifiedCached.native.queries, List.mem_append]
      exact Or.inr member
    · have tableCells : ∀ column ∈ Airbender.Compiler.TableNative.UnifiedCached.native.timestampSetupColumns, assignment.base column.address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row column := by
        intro column member
        exact setupAt column (of_decide_eq_true (List.all_eq_true.mp timestampColumns column member))
      have countCell : assignment.base (.BaseLayerWitness 56) = counts ⟨2, by decide⟩ := countsAt ⟨2, by decide⟩
      have reduced := Airbender.Compiler.HelperNative.UnifiedCached.native.timestampSourceReduction hom challenges gamma assignment helperDefined
        (Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native.helperCopies baseValue arithmetic) holds
      change (Airbender.Compiler.LookupNative.UnifiedCached.native.timestampOutput).value (assignment.value Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing hom) =
        (Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => RationalPair.leaf 1 (hom (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)) + gamma)) ++
          [NativeLookupLeaf.registryValue Airbender.Compiler.LookupNative.UnifiedCached.native.registry hom challenges gamma (assignment.value Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing hom) 13]).sum at reduced
      rw [Airbender.Compiler.TableNative.UnifiedCached.native.timestampSetupInterpreted hom challenges gamma assignment defined
        (Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row) (counts ⟨2, by decide⟩) tableCells countCell, typedEq] at reduced
      apply reduced.trans
      congr 2
      apply List.map_congr_left
      intro field member
      have same := Source.HelperField.transport_value field Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement Airbender.Compiler.HelperNative.UnifiedCached.native.placement
        Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.MemoryNative.UnifiedCached.native.bank (List.all_eq_true.mp Airbender.Compiler.HelperValidityNative.UnifiedCached.native.transportChecked field member)
        (Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts) baseValue inputAgreement
      change field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue) = _ at same
      rw [same, Airbender.Compiler.CounterFrameNative.UnifiedCached.native.helpers_preserved (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts field member]
  refine ⟨baseValue, values, ?_, rfl, externalAgreement⟩
  exact ⟨inputAgreement, arithmetic, baseLaw, affine, lookups, products, countsAt, setupAt, helpers, outputs⟩


theorem canonical_old_witness (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs.length → Source.BaseField) (counts : Fin 3 → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (baseValue : GKRAddress → Source.BaseField)
    (witness : ActualRowWitness publicTops hom challenges gamma sourceValue counts row baseValue
      (canonical publicTops hom challenges gamma baseValue)) :
    RowWitness hom challenges gamma sourceValue counts row baseValue
      (Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical hom challenges gamma baseValue) := by
  rcases witness with ⟨inputsAt, arithmetic, _, _, _, _, countsAt, setupAt, helpers, outputs⟩
  refine ⟨inputsAt, arithmetic, Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_base hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_affines hom challenges gamma baseValue arithmetic,
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_lookups hom challenges gamma baseValue,
    Airbender.Compiler.FunctionalNative.UnifiedCached.native.canonical_products hom challenges gamma baseValue, countsAt, setupAt, helpers, ?_⟩
  unfold OutputsPreserved at outputs ⊢
  change
    RationalPair.mk (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 4)) (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 5)) = _ ∧
    RationalPair.mk (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 0)) (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 1)) = _ ∧
    RationalPair.mk (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 2)) (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 3)) = _ at outputs
  rw [GenericLookup_output0_unchanged publicTops hom challenges gamma baseValue,
    GenericLookup_output1_unchanged publicTops hom challenges gamma baseValue,
    Lookup16Bits_output0_unchanged publicTops hom challenges gamma baseValue,
    Lookup16Bits_output1_unchanged publicTops hom challenges gamma baseValue,
    LookupTimestamps_output0_unchanged publicTops hom challenges gamma baseValue,
    LookupTimestamps_output1_unchanged publicTops hom challenges gamma baseValue] at outputs
  exact outputs

def BoundaryOutputsPreserved (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs.length → Source.BaseField) (fallback baseValue : GKRAddress → Source.BaseField)
    (values : GKRAddress → R) : Prop :=
  values (.InnerLayer 4 8) = (((List.finRange 2).map (fun set => windowedBoundaryToken
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.sourceValues baseValue) publicTops .terminal set.val 512)).map (memoryTokenFingerprint hom challenges)).prod ∧
  values (.InnerLayer 4 9) = (((List.finRange 2).map (fun set => windowedBoundaryToken
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.sourceValues baseValue) publicTops .initial set.val 512)).map (memoryTokenFingerprint hom challenges)).prod ∧
  values (.InnerLayer 4 6) = maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedCached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.sourceMemoryValues sourceValue fallback)))
    ((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod) ∧
  values (.InnerLayer 4 7) = maskProduct (hom (Airbender.Compiler.MemoryNative.UnifiedCached.native.sourceExecute.value (Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.sourceMemoryValues sourceValue fallback)))
    ((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows.map (fun entry => entry.fingerprint (Airbender.Compiler.MemoryFrameNative.UnifiedCached.native.sourceMemoryValues sourceValue fallback) hom challenges)).prod)

def CompleteActualRowWitness (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs.length → Source.BaseField) (counts : Fin 3 → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (fallback baseValue : GKRAddress → Source.BaseField)
    (values : GKRAddress → R) : Prop :=
  ActualRowWitness publicTops hom challenges gamma sourceValue counts row baseValue values ∧
  (∀ address, addressEqual (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.placement address)) address = false →
    baseValue address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.baseOracle row fallback address) ∧
  BoundaryOutputsPreserved publicTops hom challenges sourceValue fallback baseValue values

theorem complete_row_extends (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputs.length → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin 3 → Source.BaseField) (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      CompleteActualRowWitness publicTops hom challenges gamma sourceValue counts row fallback baseValue values := by
  obtain ⟨baseValue, values, witness, canonicalEq, externalAgreement⟩ :=
    graph_extends publicTops hom challenges gamma sourceValue original clockValid primitives counts row fallback
  subst values
  have oldWitness := canonical_old_witness publicTops hom challenges gamma sourceValue counts row baseValue witness
  have memory := Airbender.Compiler.FramedWitnessNative.UnifiedCached.memory_outputs_preserved hom challenges gamma sourceValue counts row fallback
    baseValue _ oldWitness externalAgreement
  refine ⟨baseValue, _, witness, externalAgreement,
    canonical_read_tokens publicTops hom challenges gamma baseValue,
    canonical_write_tokens publicTops hom challenges gamma baseValue, ?_, ?_⟩
  · rw [PermutationProduct_output0_unchanged publicTops hom challenges gamma baseValue]
    exact memory.2.2.1
  · rw [PermutationProduct_output1_unchanged publicTops hom challenges gamma baseValue]
    exact memory.2.2.2

theorem complete_trace_extends
    (sourceValue : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → Fin 137 → Source.BaseField)
    (original : ∀ row, Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) (sourceValue row))
    (clockValid : ∀ row, Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
    (primitives : ∀ row, Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
    (authored : ∀ row, AuthoredLookupValid (sourceValue row))
    (fallback : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → Source.BaseField) :
    ∃ counts : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → Fin 3 → Source.BaseField,
      ∀ (publicTops : Nat → Nat) {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R),
      ∃ baseValue : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → Source.BaseField,
      ∃ values : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → R,
        (∀ row, CompleteActualRowWitness publicTops hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)) ∧
        ∀ group : Fin 3, ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length).map
          (fun row => (outputPorts group).value (values row))).sum.numerator = 0 := by
  obtain ⟨counts, cancel⟩ := Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.grouped_trace_counter_witness setupColumns Airbender.Compiler.MaterializedNative.UnifiedCached.native.positive
    (fun row => sourceRequests (sourceValue row))
    (fun row => source_requests_valid (sourceValue row) (primitives row) (authored row))
  refine ⟨counts, ?_⟩
  intro publicTops R _ hom challenges gamma
  classical
  have complete (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) :
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      CompleteActualRowWitness publicTops hom challenges gamma (sourceValue row) (counts row) row (fallback row) baseValue values :=
    complete_row_extends publicTops hom challenges gamma
      (sourceValue row) (original row) (clockValid row) (primitives row) (counts row) row (fallback row)
  choose baseValue values correct using complete
  refine ⟨baseValue, values, correct, ?_⟩
  intro group
  have same : ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length).map (fun row => (outputPorts group).value (values row))) =
      ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length).map (fun row =>
        (((sourceRequests (sourceValue row) group).map (fun query => query.value hom challenges.lookupAlpha gamma)) ++
          [(Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.row (setupColumns group) row (counts row group)).value hom challenges.lookupAlpha gamma]).sum)) := by
    apply List.map_congr_left
    intro row _
    exact outputs_preserved_uniform hom challenges gamma (sourceValue row) (counts row) row (values row)
      (correct row).1.2.2.2.2.2.2.2.2.2 group
  rw [same]
  exact cancel group hom challenges.lookupAlpha gamma

theorem complete_trace_clean_extends
    (sourceValue : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → Fin 137 → Source.BaseField)
    (original : ∀ row, Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) (sourceValue row))
    (clockValid : ∀ row, Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
    (primitives : ∀ row, Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
    (authored : ∀ row, AuthoredLookupValid (sourceValue row))
    (fallback : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → Source.BaseField)
    (data : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → ProverData Source.BaseField) :
    ∃ counts : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → Fin 3 → Source.BaseField,
      ∀ (publicTops : Nat → Nat) {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R),
      ∃ baseValue : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → Source.BaseField,
      ∃ values : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → R,
        (∀ row, CompleteActualRowWitness publicTops hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)) ∧
        (∀ group : Fin 3, ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length).map
          (fun row => (outputPorts group).value (values row))).sum.numerator = 0) ∧
        ∀ row, FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment (baseValue row) (data row)) (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) Airbender.Compiler.CleanClosedNative.UnifiedCached.nativeSetup) := by
  obtain ⟨counts, constructed⟩ := complete_trace_extends sourceValue original clockValid primitives authored fallback
  refine ⟨counts, ?_⟩
  intro publicTops R _ hom challenges gamma
  obtain ⟨baseValue, values, correct, cancel⟩ := constructed publicTops hom challenges gamma
  refine ⟨baseValue, values, correct, cancel, ?_⟩
  intro row
  have witness := (correct row).1
  rcases witness with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact Airbender.Compiler.CleanClosedNative.UnifiedCached.retained_clock_from_source (sourceValue row) (counts row) (baseValue row) (data row)
    inputsAt arithmetic helpers (authored row)

end Airbender.Compiler.WindowedNative.UnifiedCached
