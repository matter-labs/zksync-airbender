import GKRProtocol.FunctionalBindings
import GKRProtocol.BaseAssignment

namespace Airbender.Compiler
set_option warningAsError true

def NativeBaseRecipe.definition (recipe : NativeBaseRecipe) (output : GKRAddress) : AffineDefinition :=
  ⟨output, recipe.toPayload⟩

def NativeBaseRecipe.relation (recipe : NativeBaseRecipe) (bank : WireBank n) (output : GKRAddress) :
    Polynomial n Source.BaseField :=
  add (atom (bank.placement output)) (negate (recipe.expression bank.placement).polynomial)

theorem NativeBaseRecipe.definition_sound [CommRing R] (recipe : NativeBaseRecipe)
    (bank : WireBank n) (output : GKRAddress) (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (base : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (inputs : ∀ address ∈ recipe.inputs, values address = hom (base address))
    (lifted : values output = hom (base output))
    (coordinates : ∀ address ∈ output :: recipe.inputs,
      base address = base (bank.address (bank.placement address)))
    (relation : evaluate (base ∘ bank.address) (recipe.relation bank output) = 0) :
    (recipe.definition output).Holds hom challenges values := by
  have same : recipe.value (base ∘ bank.address ∘ bank.placement) = recipe.value base := by
    apply AffineProgram.value_congr
    intro address member
    exact (coordinates address (List.mem_cons_of_mem _
      (by simpa only [AffineProgram.mapCoefficients_inputs] using member))).symm
  have expression : (recipe.expression bank.placement).value (base ∘ bank.address) = recipe.value base :=
    (recipe.expression_value bank.placement (base ∘ bank.address)).trans same
  have result : base output = recipe.value base := by
    have zero := relation
    simp only [NativeBaseRecipe.relation, evaluate_add, evaluate_atom, evaluate_negate,
      Expression.polynomial_value, expression, Function.comp_apply,
      ← coordinates output List.mem_cons_self, add_neg_eq_zero] at zero
    exact zero
  change values output = recipe.toPayload.interpret hom challenges values
  rw [recipe.interpret hom challenges base values inputs, lifted, result]

def NativeBaseRecipe.portsCheck (recipe : NativeBaseRecipe) (bank : WireBank n)
    (isBase : GKRAddress → Bool) (output : GKRAddress) : Bool :=
  (output :: recipe.inputs).all (fun address =>
    addressEqual (bank.address (bank.placement address)) address && isBase address)

theorem NativeBaseRecipe.definition_of_gate [CommRing R] (recipe : NativeBaseRecipe)
    (bank : WireBank n) (isBase : GKRAddress → Bool) (output : GKRAddress)
    (gate : ArithmeticGate n Source.BaseField)
    (ports : recipe.portsCheck bank isBase output = true)
    (identity : equal (recipe.relation bank output) gate.inputResidual = true)
    (checked : gate.check = true) (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (base : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (lifted : ∀ address, isBase address = true → values address = hom (base address))
    (holds : gate.expressionResidual (base ∘ bank.address) = 0) :
    (recipe.definition output).Holds hom challenges values := by
  have port (address : GKRAddress) (member : address ∈ output :: recipe.inputs) :
      bank.address (bank.placement address) = address ∧ isBase address = true := by
    have result := List.all_eq_true.mp ports address member
    simp only [Bool.and_eq_true] at result
    exact ⟨(addressEqual_iff _ _).mp result.1, result.2⟩
  apply recipe.definition_sound bank output hom challenges base values
  · intro address member
    exact lifted address (port address (List.mem_cons_of_mem _ member)).2
  · exact lifted output (port output List.mem_cons_self).2
  · intro address member
    exact congrArg base (port address member).1.symm
  · exact (equal_sound identity _).trans ((gate.checked_value checked _).trans holds)

end Airbender.Compiler
