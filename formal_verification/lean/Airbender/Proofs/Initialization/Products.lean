import Airbender.Review.Circuits.Initialization.Products
import Airbender.Proofs.Initialization.Tokens

namespace Airbender.Initialization.Proofs
set_option warningAsError true
set_option Elab.async false

variable {p : Nat} [CommRing E]

theorem matrix_product (rows : List α) (columns : List β) (value : α → β → E) :
    (rows.map fun row => (columns.map (value row)).prod).prod =
      (columns.map fun column => (rows.map fun row => value row column).prod).prod := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      exact List.prod_map_mul.symm

theorem token_list_product (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (leaves : List Leaf) (rows : List (Fin layout.rows)) :
    ((leaves.flatMap fun leaf => rows.map fun row =>
      leaf.token layout parameters raw row.val).map parameters.encode).prod =
      (leaves.map fun leaf => (rows.map fun row =>
        parameters.encode (leaf.token layout parameters raw row.val)).prod).prod := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.prod_append,
        List.map_map, List.map_cons, List.prod_cons, ih, Function.comp_def]

theorem output_token_product [Fact p.Prime] {artifact : Artifact} {tree : Tree} {phase : Phase}
    (parameters : Parameters p E) (raw : Raw p) (wires : Wires E)
    (linked : tree.Follows artifact.gates)
    (covered : tree.leaves = artifact.layout.leaves phase)
    (accepted : Accepted artifact parameters raw wires) :
    rootProduct artifact tree wires =
      ((ramTokens artifact.layout parameters raw phase).map parameters.encode).prod := by
  unfold rootProduct
  calc
    _ = ((List.finRange artifact.layout.rows).map fun row =>
        ((artifact.layout.leaves phase).map fun leaf =>
          parameters.encode (leaf.token artifact.layout parameters raw row.val)).prod).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro row _
      exact root_tokens parameters raw wires linked covered accepted row
    _ = ((artifact.layout.leaves phase).map fun leaf =>
        ((List.finRange artifact.layout.rows).map fun row =>
          parameters.encode (leaf.token artifact.layout parameters raw row.val)).prod).prod :=
      matrix_product _ _ _
    _ = _ := (token_list_product artifact.layout parameters raw
      (artifact.layout.leaves phase) (List.finRange artifact.layout.rows)).symm

end Airbender.Initialization.Proofs
