import Clean.Circuit.Expression
import Mathlib.Algebra.Field.ZMod

set_option warningAsError true

namespace Airbender.Arithmetic

/-- Proof-side spelling of the importer's unit product and zero sum nodes. -/
def nativeBooleanExpression {p : Nat} (column : Nat) : Expression (ZMod p) :=
  .mul (.mul (.const (Int.cast (1 : Int))) (.var ⟨column⟩))
    (.add (.add (.const (Int.cast (0 : Int))) (.var ⟨column⟩))
      (.const (Int.cast (-1 : Int))))

theorem nativeBooleanExpression_eq_zero {p : Nat} [Fact p.Prime]
    (column : Nat) (env : Environment (ZMod p)) :
    (nativeBooleanExpression column).eval env = 0 ↔ env.get column = 0 ∨ env.get column = 1 := by
  simp [nativeBooleanExpression, Expression.eval, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero]

end Airbender.Arithmetic
