module
public import Human.Helpers.Tables.Range

@[expose] public section

/-! Membership of honest rows in a static table of natural-number rows (the modeled G and Keccak setups): a query
    whose entries evaluate to the table's row `i` is in the table. -/

namespace Airbender.NonVacuous

/-- A query whose entries evaluate to row `i` of a static table whose rows are cast natural-number rows. -/
theorem static_contains {p w : Nat} [Fact p.Prime] {table : StaticTable (ZMod p) (fields w)}
    {rowAt : Fin table.length → Vector Nat w} (rows : ∀ i, table.row i = (rowAt i).map (fun (n : Nat) => (n : ZMod p)))
    {entry : Vector (Expression (ZMod p)) w} {env : Environment (ZMod p)} {i : Fin table.length} {row : Vector Nat w}
    (selected : rowAt i = row) (values : ∀ j : Fin w, entry[j].eval env = (row[j] : ZMod p)) :
    (Lookup.mk (Table.fromStatic table).toRaw entry).Contains env := by
  refine ⟨i, ?_⟩
  change entry.map (Expression.eval env) = table.row i
  rw [rows, selected]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, Vector.getElem_map]
  exact values ⟨j, hj⟩

end Airbender.NonVacuous
