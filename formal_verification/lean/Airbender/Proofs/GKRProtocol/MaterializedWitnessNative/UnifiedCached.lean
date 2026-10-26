import Airbender.Proofs.GKRProtocol.NativeWitness
import Airbender.Proofs.GKRProtocol.OracleFrameNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.QueryFrameNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.MaterializedRangeNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.GroupedTrace

namespace Airbender.Compiler.MaterializedWitnessNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem genericColumns : Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns.all
    (fun column => decide (column ∈ Airbender.Compiler.OracleFrameNative.UnifiedCached.native.columns)) = true := by decide +kernel

theorem range16Columns : Airbender.Compiler.TableNative.UnifiedCached.native.range16SetupColumns.all
    (fun column => decide (column ∈ Airbender.Compiler.OracleFrameNative.UnifiedCached.native.columns)) = true := by decide +kernel

theorem timestampColumns : Airbender.Compiler.TableNative.UnifiedCached.native.timestampSetupColumns.all
    (fun column => decide (column ∈ Airbender.Compiler.OracleFrameNative.UnifiedCached.native.columns)) = true := by decide +kernel

def OutputsPreserved {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (values : GKRAddress → R) : Prop :=
  (Airbender.Compiler.LookupNative.UnifiedCached.native.genericOutput).value values =
    ((Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.map (fun query =>
      query.value hom challenges.lookupAlpha gamma (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection))) ++
      [(Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.row Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns row (counts ⟨0, by decide⟩)).value hom challenges.lookupAlpha gamma]).sum
  ∧ (Airbender.Compiler.LookupNative.UnifiedCached.native.range16Output).value values =
    ((Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.map (fun query =>
      query.value hom challenges.lookupAlpha gamma (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection))) ++
      [(Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.row Airbender.Compiler.TableNative.UnifiedCached.native.range16SetupColumns row (counts ⟨1, by decide⟩)).value hom challenges.lookupAlpha gamma]).sum
  ∧ (Airbender.Compiler.LookupNative.UnifiedCached.native.timestampOutput).value values =
    ((Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => RationalPair.leaf 1
      (hom (field.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.project (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue))) + gamma))) ++
      [(Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.row Airbender.Compiler.TableNative.UnifiedCached.native.timestampSetupColumns row (counts ⟨2, by decide⟩)).value hom challenges.lookupAlpha gamma]).sum

theorem source_outputs_extends {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 145 → Source.BaseField)
    (original : Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (counts : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ Airbender.Compiler.OracleFrameNative.UnifiedCached.native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)).val < 524288) ∧
      OutputsPreserved hom challenges gamma sourceValue counts row values := by
  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, countsAt, setupAt, helpers⟩ :=
    Airbender.Compiler.OracleFrameNative.UnifiedCached.oracle_graph_extends hom challenges gamma sourceValue original clockValid primitives counts row fallback
  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, countsAt, setupAt, helpers, ?_⟩
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
    have countCell : assignment.base (.BaseLayerWitness 65) = counts ⟨0, by decide⟩ := countsAt ⟨0, by decide⟩
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
    have countCell : assignment.base (.BaseLayerWitness 63) = counts ⟨1, by decide⟩ := countsAt ⟨1, by decide⟩
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
    have countCell : assignment.base (.BaseLayerWitness 64) = counts ⟨2, by decide⟩ := countsAt ⟨2, by decide⟩
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

noncomputable def outputPorts (group : Fin 3) : RationalPorts :=
  ([Airbender.Compiler.LookupNative.UnifiedCached.native.genericOutput, Airbender.Compiler.LookupNative.UnifiedCached.native.range16Output, Airbender.Compiler.LookupNative.UnifiedCached.native.timestampOutput]).get group

def setupColumns (group : Fin 3) : List SourceSetupColumn :=
  ([Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns, Airbender.Compiler.TableNative.UnifiedCached.native.range16SetupColumns, Airbender.Compiler.TableNative.UnifiedCached.native.timestampSetupColumns]).get group

noncomputable def sourceRequests (sourceValue : Fin 145 → Source.BaseField) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.map (fun query => query.materialized (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)),
    Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.map (fun query => query.materialized (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection)),
    Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.project (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue))] 1)]).get group

def AuthoredLookupValid (sourceValue : Fin 145 → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries,
    query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 →
    Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.genericSetupColumns
      (query.fields.map (fun field => field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries,
    query.weight (RingHom.id _) (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection) ≠ 0 →
    Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains Airbender.Compiler.TableNative.UnifiedCached.native.range16SetupColumns
      (query.fields.map (fun field => field.value (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection))))

theorem outputs_preserved_uniform {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin 3 → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (values : GKRAddress → R)
    (preserved : OutputsPreserved hom challenges gamma sourceValue counts row values) :
    ∀ group : Fin 3, (outputPorts group).value values =
      (((sourceRequests sourceValue group).map (fun query => query.value hom challenges.lookupAlpha gamma)) ++
        [(Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.row (setupColumns group) row (counts group)).value hom challenges.lookupAlpha gamma]).sum := by
  intro group
  fin_cases group
  · convert preserved.1 using 1 <;> simp [outputPorts, sourceRequests, setupColumns, List.map_map, Function.comp_def]
    have coordinate : (0 : Fin 3) = (⟨0, by decide⟩ : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length) := by decide +kernel
    rw [coordinate]
  · convert preserved.2.1 using 1 <;> simp [outputPorts, sourceRequests, setupColumns, List.map_map, Function.comp_def]
    have coordinate : (1 : Fin 3) = (⟨1, by decide⟩ : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length) := by decide +kernel
    rw [coordinate]
  · convert preserved.2.2 using 1 <;> simp [outputPorts, sourceRequests, setupColumns, List.map_map, Function.comp_def]
    have coordinate : (2 : Fin 3) = (⟨2, by decide⟩ : Fin Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.length) := by decide +kernel
    rw [coordinate]

theorem source_requests_valid (sourceValue : Fin 145 → Source.BaseField)
    (primitives : Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project sourceValue))
    (authored : AuthoredLookupValid sourceValue) :
    ∀ group : Fin 3, ∀ query ∈ sourceRequests sourceValue group, query.weight ≠ 0 →
      Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.Contains (setupColumns group) query.fields := by
  intro group
  fin_cases group
  · intro query member nonzero
    change query ∈ (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.map (fun query => query.materialized (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection))) at member
    obtain ⟨item, included, same⟩ := List.mem_map.mp member
    rw [← same] at nonzero ⊢
    exact authored.1 item included nonzero
  · intro query member nonzero
    change query ∈ (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.map (fun query => query.materialized (sourceValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.originalProjection))) at member
    obtain ⟨item, included, same⟩ := List.mem_map.mp member
    rw [← same] at nonzero ⊢
    exact authored.2 item included nonzero
  · intro query member nonzero
    change query ∈ (Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.project (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue))] 1)) at member
    obtain ⟨item, included, same⟩ := List.mem_map.mp member
    rw [← same] at nonzero ⊢
    exact Airbender.Compiler.MaterializedRangeNative.UnifiedCached.native.timestamp_contains _
      (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.helper_membership sourceValue primitives item included)

def RowWitness {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin 145 → Source.BaseField)
    (counts : Fin 3 → Source.BaseField)
    (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) (baseValue : GKRAddress → Source.BaseField)
    (values : GKRAddress → R) : Prop :=
      (∀ wire, baseValue (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank.address wire) = Airbender.Compiler.CounterFrameNative.UnifiedCached.native.assigned (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.canonical sourceValue) counts wire) ∧
      (∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (baseValue ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) ∧
      (∀ address, Airbender.Compiler.FunctionalNative.UnifiedCached.native.isBase address = true → values address = hom (baseValue address)) ∧
      (∀ definition ∈ Airbender.Compiler.FunctionalNative.UnifiedCached.native.definitions, definition.Holds hom challenges values) ∧
      (∀ gate ∈ Airbender.Compiler.LookupNative.UnifiedCached.native.gates, gate.Holds hom challenges gamma values) ∧
      (∀ gate ∈ Airbender.Compiler.ProductNative.UnifiedCached.native.gates, gate.Holds hom challenges values) ∧
      (∀ index, baseValue (GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns.get index)) = counts index) ∧
      (∀ column ∈ Airbender.Compiler.OracleFrameNative.UnifiedCached.native.columns, baseValue column.address = Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.value row column) ∧
      (∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields, (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues baseValue)).val < 524288) ∧
      OutputsPreserved hom challenges gamma sourceValue counts row values

theorem native_lookup_trace_extends
    (sourceValue : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → Fin 145 → Source.BaseField)
    (original : ∀ row, Satisfies (Airbender.Compiler.SourceContractNative.UnifiedCached.native.originals.map Expression.polynomial) (sourceValue row))
    (clockValid : ∀ row, Source.clockContract Airbender.Compiler.SourceContractNative.UnifiedCached.native.clock (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
    (primitives : ∀ row, Airbender.Compiler.HelperValidityNative.UnifiedCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.UnifiedCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
      (Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement.memory.project (sourceValue row)))
    (authored : ∀ row, AuthoredLookupValid (sourceValue row))
    (fallback : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → Source.BaseField) :
    ∃ counts : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → Fin 3 → Source.BaseField,
      ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R),
      ∃ baseValue : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → Source.BaseField,
      ∃ values : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length → GKRAddress → R,
        (∀ row, RowWitness hom challenges gamma (sourceValue row) (counts row) row (baseValue row) (values row)) ∧
        ∀ group : Fin 3, ((List.finRange Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length).map
          (fun row => (outputPorts group).value (values row))).sum.numerator = 0 := by
  obtain ⟨counts, cancel⟩ := Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.grouped_trace_counter_witness setupColumns Airbender.Compiler.MaterializedNative.UnifiedCached.native.positive
    (fun row => sourceRequests (sourceValue row))
    (fun row => source_requests_valid (sourceValue row) (primitives row) (authored row))
  refine ⟨counts, ?_⟩
  intro R _ hom challenges gamma
  classical
  have complete (row : Fin Airbender.Compiler.MaterializedNative.UnifiedCached.native.model.imported.data.length) :
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      RowWitness hom challenges gamma (sourceValue row) (counts row) row baseValue values :=
    source_outputs_extends hom challenges gamma (sourceValue row) (original row) (clockValid row)
      (primitives row) (counts row) row (fallback row)
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
      (correct row).2.2.2.2.2.2.2.2.2 group
  rw [same]
  exact cancel group hom challenges.lookupAlpha gamma

end Airbender.Compiler.MaterializedWitnessNative.UnifiedCached
