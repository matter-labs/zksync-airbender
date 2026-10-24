import GKRCompiler.Reduction

namespace Airbender.Compiler
set_option warningAsError true

/-- Native lookup addition is a commutative monoid on exact numerator/denominator
pairs. This supports exact multiset preservation without dividing or excluding
challenge roots. -/
instance [CommRing R] : Zero (RationalPair R) := ⟨⟨0, 1⟩⟩
instance [CommRing R] : Add (RationalPair R) := ⟨RationalPair.add⟩

instance [CommRing R] : AddCommMonoid (RationalPair R) where
  add_assoc := by
    intro left middle right
    change (left.add middle).add right = left.add (middle.add right)
    apply congrArg₂ RationalPair.mk <;> dsimp [RationalPair.add] <;> ring
  zero_add := by
    intro pair
    change (RationalPair.mk 0 1).add pair = pair
    cases pair
    simp [RationalPair.add]
  add_zero := by
    intro pair
    change pair.add (RationalPair.mk 0 1) = pair
    cases pair
    simp [RationalPair.add]
  add_comm := by
    intro left right
    change left.add right = right.add left
    apply congrArg₂ RationalPair.mk <;> ring
  nsmul := nsmulRec

theorem LookupTree.exact_sum [CommRing R] (tree : LookupTree α)
    (primitive : α → RationalPair R) :
    tree.evaluate primitive = (tree.leaves.map primitive).sum := by
  induction tree with
  | leaf item => simp [evaluate, leaves]
  | add left right ihLeft ihRight =>
    simp only [evaluate, leaves, List.map_append, List.sum_append]
    exact congrArg₂ RationalPair.add ihLeft ihRight

theorem LookupTree.exact_source [CommRing R] (tree : LookupTree α)
    (primitive : α → RationalPair R) (source : List α) (coverage : tree.leaves.Perm source) :
    tree.evaluate primitive = (source.map primitive).sum :=
  (tree.exact_sum primitive).trans (coverage.map primitive).sum_eq

end Airbender.Compiler
