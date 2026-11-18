module
public import Human.Circuits.InitsTeardowns.Native.Products
public import Proven.InitsTeardowns.Native.Tokens

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs

variable {p : Nat} [CommRing E]

/-- Window-major native RAM tokens, the proof form of an output product.
    Noncomputable keeps the full native row domain out of compiled code. -/
noncomputable def ramTokens (layout : Layout) (parameters : Parameters p E)
    (raw : Raw p) (phase : Phase) : List (Trace.MemoryToken p) :=
  (layout.leaves phase).flatMap fun leaf =>
    (List.finRange layout.rows).map fun row => leaf.token layout parameters raw row.val

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
    (parameters : Parameters p E) (raw : Raw p) (values : Nat → GKRAddress → E)
    (linked : tree.Follows artifact.gates)
    (covered : tree.leaves = artifact.layout.leaves phase)
    (accepted : Accepted artifact parameters raw fun port row => values row (Extract.address port)) :
    outputProduct artifact tree values =
      ((ramTokens artifact.layout parameters raw phase).map parameters.encode).prod := by
  unfold outputProduct
  calc
    _ = ((List.finRange artifact.layout.rows).map fun row =>
        ((artifact.layout.leaves phase).map fun leaf =>
          parameters.encode (leaf.token artifact.layout parameters raw row.val)).prod).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro row _
      exact root_tokens parameters raw _ linked covered accepted row
    _ = ((artifact.layout.leaves phase).map fun leaf =>
        ((List.finRange artifact.layout.rows).map fun row =>
          parameters.encode (leaf.token artifact.layout parameters raw row.val)).prod).prod :=
      matrix_product _ _ _
    _ = _ := (token_list_product artifact.layout parameters raw
      (artifact.layout.leaves phase) (List.finRange artifact.layout.rows)).symm

end Airbender.InitsTeardowns.Native.Proofs
