import Airbender.Proofs.Initialization.Trees

namespace Airbender.Initialization.Proofs
set_option warningAsError true
set_option Elab.async false

variable {p : Nat} [Fact p.Prime] [CommRing E]

theorem factor_token (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) (leaf : Leaf) :
    leaf.factor layout parameters raw row = parameters.encode (leaf.token layout parameters raw row) := by
  simp [Leaf.factor, Parameters.encode, Leaf.token]

theorem root_tokens {artifact : Artifact} {tree : Tree} {phase : Phase}
    (parameters : Parameters p E) (raw : Raw p) (wires : Wires E)
    (linked : tree.Follows artifact.gates)
    (covered : tree.leaves = artifact.layout.leaves phase)
    (accepted : Accepted artifact parameters raw wires) (row : Fin artifact.layout.rows) :
    wires tree.output row.val =
      ((artifact.layout.leaves phase).map fun leaf =>
        parameters.encode (leaf.token artifact.layout parameters raw row.val)).prod := by
  rw [follows_sound artifact.layout parameters raw wires row.val linked (accepted row),
    eval_leaves, covered]
  rw [show Leaf.factor artifact.layout parameters raw row.val =
      (fun leaf => parameters.encode (leaf.token artifact.layout parameters raw row.val)) from
    funext fun leaf => factor_token artifact.layout parameters raw row.val leaf]

end Airbender.Initialization.Proofs
