import Airbender.Review.Circuits.Initialization.Model

namespace Airbender.Initialization.Proofs
set_option warningAsError true
set_option Elab.async false

variable [CommRing E]

theorem follows_sound {gates : Array Gate} {tree : Tree}
    (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (wires : Wires E) (row : Nat) (linked : tree.Follows gates)
    (accepted : ∀ gate ∈ gates.toList, gate.Sat layout parameters raw wires row) :
    wires tree.output row = tree.eval layout parameters raw row := by
  induction linked with
  | pair member => exact accepted _ member
  | product member _ _ left right =>
      exact (accepted _ member).trans (congrArg₂ (· * ·) left right)
  | copy member _ source => exact (accepted _ member).trans source

theorem eval_leaves (tree : Tree) (layout : Layout) (parameters : Parameters p E)
    (raw : Raw p) (row : Nat) :
    tree.eval layout parameters raw row =
      (tree.leaves.map (Leaf.factor layout parameters raw row)).prod := by
  induction tree with
  | pair output left right => simp [Tree.eval, Tree.leaves]
  | product output left right lhs rhs =>
      simp only [Tree.eval, Tree.leaves, List.map_append, List.prod_append, lhs, rhs]
  | copy output input source => exact source

end Airbender.Initialization.Proofs
