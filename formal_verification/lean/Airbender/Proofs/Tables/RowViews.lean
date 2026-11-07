import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- A full optional-column certificate determines the natural data row. -/
theorem unwrap_row (columns : Vector Column width) (index : Nat) (expected : Vector Nat width)
    (checked : columns.map (fun column => column.get? index) = expected.map some) :
    columns.map (fun column => (column.get? index).getD 0) = expected := by
  have converted := congrArg (Vector.map (fun value : Option Nat => value.getD 0)) checked
  simpa only [Vector.map_map, Function.comp_def, Option.getD_some, Vector.map_id'] using converted

/-- Pointwise imported-column agreement determines the whole natural row. -/
theorem rows_agree (left right : TableData width) (index : Nat)
    (checked : ∀ lane : Fin width, left.columns[lane].get? index = right.columns[lane].get? index) :
    left.columns.map (fun column => (column.get? index).getD 0) =
      right.columns.map (fun column => (column.get? index).getD 0) := by
  apply Vector.ext
  intro lane bound
  simp only [Vector.getElem_map]
  exact congrArg (fun value => value.getD 0) (checked ⟨lane, bound⟩)

end Airbender.Setup.Proofs
