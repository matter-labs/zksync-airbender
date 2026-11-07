import Clean.Circuit.Expression
import Mathlib.Data.ZMod.Basic

namespace Airbender.Arithmetic

/-- A literal linear expression retains the importer's zero sum and unit product
    nodes. Native bindings below check the complete expression tree. -/
def linearExpression {p : Nat} (constant : Int) (terms : List (Int × Nat)) :
    Expression (ZMod p) :=
  terms.foldl (fun accumulated term =>
    .add accumulated (.mul (.mul (.const (Int.cast (1 : Int))) (.const (Int.cast term.1)))
      (.var ⟨term.2⟩)))
    (.add (.const (Int.cast (0 : Int))) (.const (Int.cast constant)))

end Airbender.Arithmetic
