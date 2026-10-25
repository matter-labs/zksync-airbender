import GKRProtocol.TraceAggregation

namespace Airbender.Compiler
set_option warningAsError true

/-- A source request, retaining its weight separately from its field payload. -/
structure MaterializedQuery where
  fields : List Source.BaseField
  weight : Source.BaseField

def MaterializedQuery.value {R : Type} [CommRing R] (query : MaterializedQuery)
    (hom : Source.BaseField →+* R) (alpha gamma : R) : RationalPair R :=
  RationalPair.leaf (hom query.weight)
    (NativeLookupEncoding.linearize hom alpha query.fields 0 0 + gamma)

def SourceLookupQuery.materialized (query : SourceLookupQuery) (source : Nat → Source.BaseField) : MaterializedQuery :=
  ⟨query.fields.map (fun field => field.value source), query.weight (RingHom.id _) source⟩

theorem SourceLookupQuery.weight_hom {R : Type} [CommRing R] (query : SourceLookupQuery)
    (hom : Source.BaseField →+* R) (source : Nat → Source.BaseField) :
    hom (query.weight (RingHom.id _) source) = query.weight hom source := by
  cases mask : query.mask <;> simp [weight, mask]

@[simp] theorem SourceLookupQuery.materialized_value {R : Type} [CommRing R] (query : SourceLookupQuery)
    (hom : Source.BaseField →+* R) (alpha gamma : R) (source : Nat → Source.BaseField) :
    (query.materialized source).value hom alpha gamma = query.value hom alpha gamma source := by
  unfold MaterializedQuery.value materialized value
  rw [weight_hom]

@[simp] theorem MaterializedQuery.scalar_value {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (alpha gamma : R) (value : Source.BaseField) :
    (MaterializedQuery.mk [value] 1).value hom alpha gamma = RationalPair.leaf 1 (hom value + gamma) := by
  simp [MaterializedQuery.value, NativeLookupEncoding.linearize]

/-- All lookup groups receive one common pre-challenge vector of base-field
multiplicities; their exact native pair aggregates have zero numerators. -/
theorem MaterializedLookupSetup.grouped_trace_counter_witness (model : MaterializedLookupSetup width)
    (columns : G → List SourceSetupColumn) (positive : 0 < model.imported.data.length)
    (queries : Fin model.imported.data.length → G → List MaterializedQuery)
    (valid : ∀ row group, ∀ query ∈ queries row group, query.weight ≠ 0 →
      model.Contains (columns group) query.fields) :
    ∃ counts : Fin model.imported.data.length → G → Source.BaseField,
      ∀ group, ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (alpha gamma : R),
      ((List.finRange model.imported.data.length).map (fun row =>
        (((queries row group).map (fun query => query.value hom alpha gamma)) ++
          [(model.row (columns group) row (counts row group)).value hom alpha gamma]).sum)).sum.numerator = 0 := by
  classical
  have complete (group : G) := model.trace_counter_witness (columns group) positive
    (fun row => queries row group) (fun _ query => query.fields) (fun _ query => query.weight)
    (fun row query member nonzero => valid row group query member nonzero)
  refine ⟨fun row group => (complete group).choose row, ?_⟩
  intro group R _ hom alpha gamma
  exact (complete group).choose_spec hom alpha gamma

end Airbender.Compiler
