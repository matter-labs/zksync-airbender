import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Airbender.Compiler
set_option warningAsError true

/-- The actual numerator/denominator representation used by the lookup gates.
No inversion occurs while reducing the graph. -/
structure RationalPair (R : Type) where
  numerator : R
  denominator : R
  deriving Repr, DecidableEq

def RationalPair.add [CommRing R] (left right : RationalPair R) : RationalPair R :=
  ⟨left.numerator * right.denominator + left.denominator * right.numerator,
    left.denominator * right.denominator⟩

def RationalPair.leaf [CommRing R] (numerator denominator : R) : RationalPair R :=
  ⟨numerator, denominator⟩

def RationalPair.Represents [CommRing R] (pair : RationalPair R) (value : R) : Prop :=
  pair.numerator = pair.denominator * value

/-- Addition of the native pairs preserves the represented sum, even when an
intermediate denominator vanishes. Nonzero assumptions are needed only for
interpreting a primitive fraction or recovering a quotient at the boundary. -/
theorem RationalPair.add_represents [CommRing R] {left right : RationalPair R} {a b : R}
    (hl : left.Represents a) (hr : right.Represents b) :
    (left.add right).Represents (a + b) := by
  dsimp [Represents] at hl hr ⊢
  simp only [add, hl, hr]
  ring

theorem RationalPair.leaf_represents [Field R] (numerator denominator : R)
    (nonzero : denominator ≠ 0) :
    (leaf numerator denominator).Represents (numerator / denominator) := by
  simp only [Represents, leaf]
  field_simp [nonzero]

theorem RationalPair.quotient [Field R] {pair : RationalPair R} {value : R}
    (represents : pair.Represents value) (nonzero : pair.denominator ≠ 0) :
    pair.numerator / pair.denominator = value := by
  rw [represents]
  exact mul_div_cancel_left₀ value nonzero

/-- Scalar/vector lookup pairs share these formulas after materialization.
The additive challenge is mixed exactly once into each primitive denominator. -/
def lookupPair [CommRing R] (gamma a b : R) : RationalPair R :=
  ⟨(a + gamma) + (b + gamma), (a + gamma) * (b + gamma)⟩

def lookupMinusSetup [CommRing R] (gamma mask input multiplicity setup : R) : RationalPair R :=
  ⟨mask * (setup + gamma) - multiplicity * (input + gamma),
    (input + gamma) * (setup + gamma)⟩

def lookupRemainder [CommRing R] (gamma : R) (pair : RationalPair R) (input : R) : RationalPair R :=
  ⟨pair.numerator * (input + gamma) + pair.denominator,
    pair.denominator * (input + gamma)⟩

theorem lookupPair_is_add [CommRing R] (gamma a b : R) :
    lookupPair gamma a b = (RationalPair.leaf 1 (a + gamma)).add
      (RationalPair.leaf 1 (b + gamma)) := by
  simp [lookupPair, RationalPair.leaf, RationalPair.add, add_comm]

theorem lookupMinusSetup_is_add [CommRing R] (gamma mask input multiplicity setup : R) :
    lookupMinusSetup gamma mask input multiplicity setup =
      (RationalPair.leaf mask (input + gamma)).add
      (RationalPair.leaf (-multiplicity) (setup + gamma)) := by
  apply congrArg₂ RationalPair.mk
  · change mask * (setup + gamma) - multiplicity * (input + gamma) =
      mask * (setup + gamma) + (input + gamma) * (-multiplicity)
    ring
  · rfl

theorem lookupRemainder_is_add [CommRing R] (gamma : R) (pair : RationalPair R) (input : R) :
    lookupRemainder gamma pair input = pair.add (RationalPair.leaf 1 (input + gamma)) := by
  simp [lookupRemainder, RationalPair.add, RationalPair.leaf]

inductive LookupTree (α : Type) where
  | leaf : α → LookupTree α
  | add : LookupTree α → LookupTree α → LookupTree α
  deriving Repr, DecidableEq

def LookupTree.leaves : LookupTree α → List α
  | .leaf item => [item]
  | .add left right => left.leaves ++ right.leaves

def LookupTree.evaluate [CommRing R] (primitive : α → RationalPair R) : LookupTree α → RationalPair R
  | .leaf item => primitive item
  | .add left right => (left.evaluate primitive).add (right.evaluate primitive)

theorem LookupTree.represents [CommRing R] (tree : LookupTree α)
    (primitive : α → RationalPair R) (meaning : α → R)
    (leaves : ∀ item ∈ tree.leaves, (primitive item).Represents (meaning item)) :
    (tree.evaluate primitive).Represents ((tree.leaves.map meaning).sum) := by
  induction tree with
  | leaf item => simpa [evaluate, LookupTree.leaves] using leaves item (by simp [LookupTree.leaves])
  | add left right ihLeft ihRight =>
    have hl := ihLeft (fun item member => leaves item (List.mem_append_left _ member))
    have hr := ihRight (fun item member => leaves item (List.mem_append_right _ member))
    simpa only [evaluate, LookupTree.leaves, List.map_append, List.sum_append] using
      RationalPair.add_represents hl hr

/-- Coverage uses an exact multiset of primitive requests, preserving duplicate
queries and multiplicities. A set-membership check would be insufficient. -/
theorem LookupTree.source_sum [CommRing R] (tree : LookupTree α)
    (primitive : α → RationalPair R) (meaning : α → R) (source : List α)
    (coverage : tree.leaves.Perm source)
    (leaves : ∀ item ∈ source, (primitive item).Represents (meaning item)) :
    (tree.evaluate primitive).Represents ((source.map meaning).sum) := by
  have result := tree.represents primitive meaning (fun item member => leaves item (coverage.mem_iff.mp member))
  rw [(coverage.map meaning).sum_eq] at result
  exact result

inductive ProductTree (α : Type) where
  | leaf : α → ProductTree α
  | mul : ProductTree α → ProductTree α → ProductTree α
  deriving Repr, DecidableEq

def ProductTree.leaves : ProductTree α → List α
  | .leaf item => [item]
  | .mul left right => left.leaves ++ right.leaves

def ProductTree.evaluate [CommMonoid R] (primitive : α → R) : ProductTree α → R
  | .leaf item => primitive item
  | .mul left right => left.evaluate primitive * right.evaluate primitive

theorem ProductTree.product [CommMonoid R] (tree : ProductTree α) (primitive : α → R) :
    tree.evaluate primitive = (tree.leaves.map primitive).prod := by
  induction tree with
  | leaf item => simp [evaluate, leaves]
  | mul left right ihLeft ihRight => simp [evaluate, leaves, ihLeft, ihRight]

theorem ProductTree.source_product [CommMonoid R] (tree : ProductTree α)
    (primitive : α → R) (source : List α) (coverage : tree.leaves.Perm source) :
    tree.evaluate primitive = (source.map primitive).prod :=
  (tree.product primitive).trans (coverage.map primitive).prod_eq

def maskProduct [CommRing R] (mask input : R) : R := (input - 1) * mask + 1

theorem maskProduct_active [CommRing R] (input : R) : maskProduct 1 input = input := by
  simp [maskProduct]

theorem maskProduct_inactive [CommRing R] (input : R) : maskProduct 0 input = 1 := by
  simp [maskProduct]

end Airbender.Compiler
