import Airbender.Proofs.GKRProtocol.UniformCounters

namespace Airbender.Compiler
set_option warningAsError true

/-- The prover's sum of per-row output pairs is the exact pooled query sum
followed by every setup row, including padding rows. -/
theorem rational_row_aggregation {R I : Type} [CommRing R]
    (rows : List I) (queries : I → List (RationalPair R)) (setup : I → RationalPair R) :
    (rows.map (fun row => (queries row ++ [setup row]).sum)).sum =
      (rows.flatMap queries ++ rows.map setup).sum := by
  induction rows with
  | nil => rfl
  | cons row rest proof =>
      simp only [List.map_cons, List.sum_cons, List.sum_append,
        List.flatMap_cons] at *
      rw [proof]
      ac_rfl

/-- A single table multiplicity assignment works for every extension ring and
all challenge values. Queries are identified by occurrence and trace row. -/
theorem MaterializedLookupSetup.trace_counter_witness (model : MaterializedLookupSetup width)
    (columns : List SourceSetupColumn) (positive : 0 < model.imported.data.length)
    (queries : Fin model.imported.data.length → List Q)
    (queryFields : Fin model.imported.data.length → Q → List Source.BaseField)
    (weight : Fin model.imported.data.length → Q → Source.BaseField)
    (valid : ∀ row, ∀ query ∈ queries row, weight row query ≠ 0 →
      model.Contains columns (queryFields row query)) :
    ∃ counts : Fin model.imported.data.length → Source.BaseField,
      ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (alpha gamma : R),
      ((List.finRange model.imported.data.length).map (fun row =>
        ((queries row).map (fun query => RationalPair.leaf (hom (weight row query))
          (NativeLookupEncoding.linearize hom alpha (queryFields row query) 0 0 + gamma)) ++
          [(model.row columns row (counts row)).value hom alpha gamma]).sum)).sum.numerator = 0 := by
  let entries := (List.finRange model.imported.data.length).flatMap (fun row =>
    (queries row).map (fun query => (row, query)))
  obtain ⟨counts, correct⟩ := model.uniform_counter_witness columns positive entries
    (fun entry => queryFields entry.1 entry.2) (fun entry => weight entry.1 entry.2) (by
      intro entry member nonzero
      obtain ⟨row, _, included⟩ := List.mem_flatMap.mp member
      obtain ⟨query, queryMember, same⟩ := List.mem_map.mp included
      rw [← same] at nonzero ⊢
      exact valid row query queryMember nonzero)
  refine ⟨counts, ?_⟩
  intro R _ hom alpha gamma
  rw [rational_row_aggregation]
  have pooled := correct hom alpha gamma
  simpa only [entries, List.map_flatMap, List.map_map, Function.comp_def] using pooled

end Airbender.Compiler
