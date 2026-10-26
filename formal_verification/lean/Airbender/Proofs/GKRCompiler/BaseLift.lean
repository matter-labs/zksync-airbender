import Airbender.Proofs.GKRCompiler.HomPolynomial

namespace Airbender.Compiler
set_option warningAsError true

theorem Expression.valueHom_at_hom [CommRing F] [CommRing R] (expression : Expression n F)
    (hom : F →+* R) (values : Fin n → F) :
    expression.valueHom hom (hom ∘ values) = hom (expression.value values) := by
  rw [← expression.polynomial_valueHom, evaluateHom_at_hom, expression.polynomial_value]

def ArithmeticGate.residualHom [CommRing F] [CommRing R] (hom : F →+* R)
    (values : Fin n → R) : ArithmeticGate n F → R
  | .assertZero _ expression => expression.valueHom hom values
  | .define output _ expression => values output - expression.valueHom hom values
  | .copy output input => values output - values input

theorem ArithmeticGate.residualHom_at_hom [CommRing F] [CommRing R] (gate : ArithmeticGate n F)
    (hom : F →+* R) (values : Fin n → F) :
    gate.residualHom hom (hom ∘ values) = hom (gate.expressionResidual values) := by
  cases gate with
  | assertZero input expression => exact expression.valueHom_at_hom hom values
  | define output input expression =>
      simp only [residualHom, Expression.valueHom_at_hom, Function.comp_apply, expressionResidual, map_sub]
  | copy output input => simp only [residualHom, Function.comp_apply, expressionResidual, map_sub]

/-- Accepted extension-field arithmetic yields base-field constraints only
through an injective embedding. Forward witness construction needs no such
assumption; the actual nontrivial extension field supplies it at soundness. -/
theorem ArithmeticGate.base_of_lifted [CommRing F] [CommRing R] (gate : ArithmeticGate n F)
    (hom : F →+* R) (injective : Function.Injective hom) (values : Fin n → F)
    (holds : gate.residualHom hom (hom ∘ values) = 0) : gate.expressionResidual values = 0 := by
  apply injective
  rw [map_zero]
  exact (gate.residualHom_at_hom hom values).symm.trans holds

end Airbender.Compiler
