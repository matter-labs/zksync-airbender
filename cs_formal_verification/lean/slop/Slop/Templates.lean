module
public import Slop.Constraints
public import Human.Helpers.Properties
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
Templates for imported constraints and queries: the expression nodes the importer writes, so that
a family of constraints (one per limb, per port, per flag) is stated once as a function of its index
and checked against the imported list by one closed fact per index (`op_index` + `rfl`). Proofs
evaluate the template once, for every index, instead of unfolding the constraint list
(lean-strategies §2.1).
-/

namespace Airbender.Templates
set_option warningAsError true

/-- The integer constant `c` as the importer writes it. -/
abbrev constant {p : Nat} (c : Int) : Expression (ZMod p) := Expression.const (c : ZMod p)

abbrev cell {p : Nat} (i : Nat) : Expression (ZMod p) := Expression.var ⟨i⟩

/-- `1 * a * b`. -/
abbrev product {p : Nat} (a b : Expression (ZMod p)) : Expression (ZMod p) :=
  ((constant (Int.ofNat 1)).mul a).mul b

/-- `x * y` for two columns. -/
abbrev pair {p : Nat} (x y : Nat) : Expression (ZMod p) := product (cell x) (cell y)

/-- `acc + t₁ + … + tₙ`, left-nested as the importer writes sums. -/
abbrev sumFrom {p : Nat} (acc : Expression (ZMod p)) (terms : List (Expression (ZMod p))) :
    Expression (ZMod p) :=
  terms.foldl Expression.add acc

/-- A column as a query entry: `0 + 0 + 1 * 1 * x`. -/
abbrev entry {p : Nat} (x : Nat) : Expression (ZMod p) :=
  ((constant (Int.ofNat 0)).add (constant (Int.ofNat 0))).add
    (product (constant (Int.ofNat 1)) (cell x))

/-- A constant query column: `0 + t`. -/
abbrev tagEntry {p : Nat} (t : Nat) : Expression (ZMod p) :=
  (constant (Int.ofNat 0)).add (constant (Int.ofNat t))

/-- The Boolean constraint `x * (x - 1)`. -/
abbrev flag {p : Nat} (x : Nat) : Expression (ZMod p) :=
  ((constant (Int.ofNat 1)).mul (cell x)).mul
    (((constant (Int.ofNat 0)).add (cell x)).add (constant (Int.negSucc 0)))

variable {p : Nat} [Fact p.Prime]

theorem entry_eval (w : Nat → ZMod p) (x : Nat) :
    (entry x : Expression (ZMod p)).eval (Verification.environment w) = w x := by
  simp only [Expression.eval, Verification.environment]
  push_cast
  ring

theorem tag_eval (w : Nat → ZMod p) (t : Nat) :
    (tagEntry t : Expression (ZMod p)).eval (Verification.environment w) = (t : ZMod p) := by
  simp [Expression.eval]

/-- A Boolean constraint that holds forces its column to be a bit. -/
theorem flag_bit {w : Nat → ZMod p} {ops : List (FlatOperation (ZMod p))}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) ops)
    {k : Nat} {hk : k < (FlatOperation.constraints ops).length} {x : Nat}
    (shape : (FlatOperation.constraints ops).get ⟨k, hk⟩ = flag x) : w x = 0 ∨ w x = 1 := by
  have zero := Verification.assertion_of_holds h ⟨k, hk⟩
  rw [shape] at zero
  simp only [Expression.eval, Verification.environment] at zero
  push_cast at zero
  rcases mul_eq_zero.mp zero with zero | one
  · exact Or.inl (by simpa using zero)
  · exact Or.inr (by linear_combination one)

end Airbender.Templates
