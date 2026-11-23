module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanArguments
public import Proven.GKRProtocol.HelperCertificate

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler

theorem NativeBaseRecipe.expression_at (recipe : NativeBaseRecipe) (bank : WireBank n)
    (checked : bank.check recipe = true) (base : GKRAddress → Source.BaseField) :
    (recipe.expression bank.placement).value (base ∘ bank.address) = recipe.value base := by
  rw [recipe.expression_value]
  apply AffineProgram.value_congr
  intro address member
  have contained : address ∈ recipe.inputs := by
    simpa only [AffineProgram.mapCoefficients_inputs] using member
  exact (bank.wires checked base address contained).symm

theorem CleanExpression.helper_value (expression : Airbender.Expression Source.BaseField)
    (placement : Nat → Fin n) (fullBank : WireBank n)
    (recipe : NativeBaseRecipe) (nativeBank : WireBank m)
    (checked : nativeCheck expression placement fullBank (recipe.expression nativeBank.placement) nativeBank = true)
    (inBank : nativeBank.check recipe = true)
    (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    expression.eval ⟨fun index => base (fullBank.address (placement index)), data⟩ = recipe.value base :=
  (native_value expression placement fullBank (recipe.expression nativeBank.placement) nativeBank checked base data).trans
    (recipe.expression_at nativeBank inBank base)

end Airbender.Compiler
