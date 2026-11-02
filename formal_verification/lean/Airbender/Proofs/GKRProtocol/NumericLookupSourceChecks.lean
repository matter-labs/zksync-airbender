import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks

namespace Airbender.Compiler.NumericLookupSourceChecks
set_option warningAsError true
open NumericFunctionalBaseChecks

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

def ofFlag (flag : Bool) : Typed n babyBearModulus :=
  ⟨[⟨.BaseLayerWitness 0, .BaseLayerWitness 0, flag⟩], [], []⟩

theorem ofFlag_check (flag : Bool) :
    (ofFlag (n := n) flag).check = flag := by
  cases flag <;> rfl

def ofAgreement {relations : List (Polynomial n Source.BaseField)}
    {recipe : NativeBaseRecipe} (agreement : BaseRecipeAgreement relations recipe)
    (sourcePlacement : Nat → Fin n) (bank : WireBank n) : Typed n babyBearModulus :=
  let original := (agreement.field bank.placement).agreement sourcePlacement
  ⟨recipe.inputs.map (fun address => ⟨address, bank.address (bank.placement address), true⟩),
    original.source, add original.lowered (combination relations original.witness)⟩

/-- Keep the complete original witness and both original check predicates. -/
theorem ofAgreement_check {relations : List (Polynomial n Source.BaseField)}
    {recipe : NativeBaseRecipe} (agreement : BaseRecipeAgreement relations recipe)
    (sourcePlacement : Nat → Fin n) (bank : WireBank n) :
    (ofAgreement agreement sourcePlacement bank).check =
      (bank.check recipe && agreement.check sourcePlacement bank.placement) := by
  simp only [ofAgreement, Typed.check, List.all_map, Function.comp_def,
    TypedPort.check, Bool.and_true, WireBank.check, BaseRecipeAgreement.check,
    LookupFieldAgreement.check, Agreement.check]

end Airbender.Compiler.NumericLookupSourceChecks
