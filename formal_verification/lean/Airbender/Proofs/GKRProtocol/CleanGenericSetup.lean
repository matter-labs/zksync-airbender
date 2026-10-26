import Airbender.Proofs.GKRProtocol.MaterializedSetup
import Airbender.Proofs.GKRProtocol.LookupSourceSemantics
import Airbender.Proofs.BabyBear

namespace Airbender.Compiler
set_option warningAsError true

/-- The source generic lookup payload is exactly the vector row exposed by the
retained Clean setup table, including its final selector column when present. -/
theorem MaterializedLookupSetup.generic_fields (model : MaterializedLookupSetup width)
    (row : Fin model.imported.data.length) :
    model.fields ((List.range width).map SourceSetupColumn.generic) row =
      ((model.imported.data.row row).map (fun entry : Int => (entry : Source.BaseField))).toList := by
  let entries := ((model.imported.data.row row).map (fun entry : Int => (entry : Source.BaseField))).toList
  have length : entries.length = width := by simp [entries]
  change model.fields ((List.range width).map SourceSetupColumn.generic) row = entries
  conv_rhs => rw [← List.map_range_getD entries 0, length]
  simp only [MaterializedLookupSetup.fields, List.map_map]
  apply List.map_congr_left
  intro column member
  have bound := List.mem_range.mp member
  simp only [Function.comp_def]
  rw [model.value_generic row ⟨column, bound⟩]
  simp [entries, bound]

theorem MaterializedLookupSetup.generic_clean_contains (model : MaterializedLookupSetup width)
    (columns : List SourceSetupColumn)
    (inventory : columns = (List.range width).map SourceSetupColumn.generic)
    (value : Vector Source.BaseField width) (member : model.Contains columns value.toList)
    (name : String) (provided : Array (Vector Source.BaseField width)) :
    (model.imported.data.table (p := babyBearModulus) name).Contains provided value := by
  obtain ⟨row, same⟩ := member
  change ∃ index : Fin model.imported.data.length,
    value = (model.imported.data.row index).map (fun entry : Int => (entry : Source.BaseField))
  refine ⟨row, Vector.toList_inj.mp ?_⟩
  rw [inventory, model.generic_fields row] at same
  exact same

end Airbender.Compiler
