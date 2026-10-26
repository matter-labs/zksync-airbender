import Airbender.Proofs.GKRProtocol.MaterializedCounters

namespace Airbender.Compiler
set_option warningAsError true

/-- Materialized table membership of enabled source queries constructs actual
base-field multiplicities before the extension ring or challenges are chosen. The native rational sum has zero numerator at every
challenge, including roots of primitive denominators. -/
theorem MaterializedLookupSetup.uniform_counter_witness
    (model : MaterializedLookupSetup width) (columns : List SourceSetupColumn)
    (positive : 0 < model.imported.data.length) (entries : List Q)
    (queryFields : Q → List Source.BaseField) (weight : Q → Source.BaseField)
    (valid : ∀ entry ∈ entries, weight entry ≠ 0 → model.Contains columns (queryFields entry))
    : ∃ counts : Fin model.imported.data.length → Source.BaseField,
      ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (alpha gamma : R),
      ((entries.map (fun entry => RationalPair.leaf (hom (weight entry))
        (NativeLookupEncoding.linearize hom alpha (queryFields entry) 0 0 + gamma))) ++
        ((List.finRange model.imported.data.length).map
          (fun row => (model.row columns row (counts row)).value hom alpha gamma))).sum.numerator = 0 := by
  classical
  let enabled := fun entry => decide (weight entry ≠ 0)
  let active := entries.filter enabled
  let label : Q → Fin model.imported.data.length := fun entry =>
    if found : model.Contains columns (queryFields entry) then found.choose else ⟨0, positive⟩
  have labelCorrect (entry : Q) (contained : model.Contains columns (queryFields entry)) :
      queryFields entry = model.fields columns (label entry) := by
    dsimp only [label]
    rw [dif_pos contained]
    exact contained.choose_spec
  let counts := fun row => lookupCount row active label weight
  refine ⟨counts, ?_⟩
  intro R _ hom alpha gamma
  let queryDenominator := fun entry => NativeLookupEncoding.linearize hom alpha (queryFields entry) 0 0 + gamma
  let tableDenominator := fun row => NativeLookupEncoding.linearize hom alpha (model.fields columns row) 0 0 + gamma
  have countHom (row : Fin model.imported.data.length) :
      hom (counts row) = lookupCount row active label (fun entry => hom (weight entry)) :=
    lookupCount_hom hom row active label weight
  have setupSame : ((List.finRange model.imported.data.length).map
      (fun row => (model.row columns row (counts row)).value hom alpha gamma)) =
      lookupSetupTerms (List.finRange model.imported.data.length) active label
        (fun entry => hom (weight entry)) tableDenominator := by
    apply List.map_congr_left
    intro row _
    rw [model.row_value, countHom]
  rw [setupSame]
  apply canonicalMaskedLookupCounts_zero (List.finRange model.imported.data.length) entries enabled label
    (fun entry => hom (weight entry)) queryDenominator tableDenominator
  · exact List.nodup_finRange _
  · intro entry _
    simp
  · intro entry member
    have filtered := List.mem_filter.mp member
    have nonzero : weight entry ≠ 0 := of_decide_eq_true filtered.2
    have same := labelCorrect entry (valid entry filtered.1 nonzero)
    exact congrArg (fun fields => NativeLookupEncoding.linearize hom alpha fields 0 0 + gamma) same
  · intro entry member
    have condition := (List.mem_filter.mp member).2
    have zero : weight entry = 0 := by simpa [enabled] using condition
    rw [zero, map_zero]

end Airbender.Compiler
