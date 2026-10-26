import Airbender.Proofs.GKRProtocol.CleanArithmetic
import Airbender.Proofs.GKRProtocol.CanonicalSource
import Airbender.Proofs.BabyBear

namespace Airbender.Compiler
set_option warningAsError true

def CleanExpression.nativeCheck (expression : _root_.Expression Source.BaseField)
    (placement : Nat → Fin n) (fullBank : WireBank n)
    (native : Expression m Source.BaseField) (nativeBank : WireBank m) : Bool :=
  native.polynomial.all (fun term => term.2.all (fun wire =>
    decide (fullBank.address (fullBank.placement (nativeBank.address wire)) = nativeBank.address wire))) &&
    equal (polynomial placement expression)
      (rename (fullBank.placement ∘ nativeBank.address) native.polynomial)

theorem CleanExpression.native_value (expression : _root_.Expression Source.BaseField)
    (placement : Nat → Fin n) (fullBank : WireBank n)
    (native : Expression m Source.BaseField) (nativeBank : WireBank m)
    (checked : nativeCheck expression placement fullBank native nativeBank = true)
    (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    expression.eval ⟨fun index => base (fullBank.address (placement index)), data⟩ =
      native.value (base ∘ nativeBank.address) := by
  have clauses : native.polynomial.all (fun term => term.2.all (fun wire =>
      decide (fullBank.address (fullBank.placement (nativeBank.address wire)) = nativeBank.address wire))) = true ∧
      equal (polynomial placement expression)
        (rename (fullBank.placement ∘ nativeBank.address) native.polynomial) = true := by
    simpa only [nativeCheck, Bool.and_eq_true] using checked
  rw [← polynomial_value expression placement (base ∘ fullBank.address)
    ⟨fun index => base (fullBank.address (placement index)), data⟩ (fun _ _ => rfl)]
  rw [equal_sound clauses.2, evaluate_rename, ← Expression.polynomial_value]
  apply evaluate_congr_on
  intro term member wire included
  have address : fullBank.address (fullBank.placement (nativeBank.address wire)) = nativeBank.address wire :=
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp clauses.1 term member) wire included)
  exact congrArg base address

end Airbender.Compiler
