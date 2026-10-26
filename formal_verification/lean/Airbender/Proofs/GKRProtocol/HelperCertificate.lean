import Airbender.Proofs.GKRProtocol.HelperSource
import Airbender.Proofs.GKRProtocol.BaseEncoding
import Airbender.Proofs.GKRProtocol.LookupSourceSemantics

namespace Airbender.Compiler
set_option warningAsError true

structure HelperAgreement (relations : List (Polynomial n Source.BaseField)) (recipe : NativeBaseRecipe) where
  source : Source.HelperField
  witness : Combination relations

def HelperAgreement.agreement {relations : List (Polynomial n Source.BaseField)} {recipe : NativeBaseRecipe}
    (candidate : HelperAgreement relations recipe) (placement : Source.HelperPlacement n)
    (bank : WireBank n) : Agreement relations :=
  ⟨candidate.source.polynomial placement, (recipe.expression bank.placement).polynomial, candidate.witness⟩

def HelperAgreement.check {relations : List (Polynomial n Source.BaseField)} {recipe : NativeBaseRecipe}
    (candidate : HelperAgreement relations recipe) (placement : Source.HelperPlacement n) (bank : WireBank n) : Bool :=
  (candidate.agreement placement bank).check

theorem HelperAgreement.sound {relations : List (Polynomial n Source.BaseField)} {recipe : NativeBaseRecipe}
    (candidate : HelperAgreement relations recipe) (placement : Source.HelperPlacement n) (bank : WireBank n)
    (checked : candidate.check placement bank = true) (inBank : bank.check recipe = true)
    (base : GKRAddress → Source.BaseField) (copies : Satisfies relations (base ∘ bank.address)) :
    candidate.source.value (placement.project (base ∘ bank.address)) = recipe.value base := by
  have same := Agreement.sound checked copies
  change evaluate (base ∘ bank.address) (candidate.source.polynomial placement) =
    evaluate (base ∘ bank.address) (recipe.expression bank.placement).polynomial at same
  rw [candidate.source.polynomial_value, Expression.polynomial_value, recipe.expression_value] at same
  apply same.trans
  apply Eq.symm
  apply AffineProgram.value_congr
  simpa only [AffineProgram.mapCoefficients_inputs, Function.comp_apply] using bank.wires inBank base

/-- Relate a consumed native timestamp operand to its independently derived
source helper field. Affine definitions, typing and copy equations are actual
native relations, not replacement equations supplied by the certificate. -/
theorem NativeLookupLeaf.source_helper [CommRing R] (leaf : NativeLookupLeaf) (recipe : NativeBaseRecipe)
    (typing : ConsumerTyping) (roles : (NativeLookupEncoding.scalar recipe).baseCheck typing = true)
    (definitions : List AffineDefinition) (indices : List Nat)
    (expanded : LookupPayload.expand definitions indices leaf.payload = some recipe.toPayload)
    (weight : leaf.weight = .one) (assignment : TypedAssignment R) (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) (gamma : R)
    (defined : ∀ definition ∈ definitions, definition.Holds hom challenges (assignment.value typing hom))
    (field : Source.HelperField) (values : Source.HelperValues)
    (same : field.value values = recipe.value assignment.base) :
    leaf.value hom challenges gamma (assignment.value typing hom) =
      RationalPair.leaf 1 (hom (field.value values) + gamma) := by
  have inputRoles : ∀ address ∈ recipe.inputs, typing.compatible (address, .base) = true := by
    simpa only [NativeLookupEncoding.baseCheck, NativeLookupEncoding.columns,
      List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true] using roles
  have payload := (LookupPayload.expand_sound hom challenges (assignment.value typing hom) defined expanded).symm.trans
    (recipe.interpret hom challenges assignment.base (assignment.value typing hom)
      (fun address member => assignment.value_base typing hom (inputRoles address member)))
  simp only [NativeLookupLeaf.value, weight, LookupWeight.value, payload, ← same]

theorem helper_sum_translation [AddCommMonoid R] (primitive : Nat → R) (source : List R)
    {native labels : List Nat}
    (fields : List.Forall₂ (fun index label => primitive index = (source[label]?).getD 0) native labels)
    (coverage : labels.Perm (List.range source.length)) :
    (native.map primitive).sum = source.sum := by
  have same : native.map primitive = labels.map (fun index => (source[index]?).getD 0) := by
    clear coverage
    induction fields with
    | nil => rfl
    | cons first rest proof => exact congrArg₂ List.cons first proof
  rw [same, (coverage.map (fun index => (source[index]?).getD 0)).sum_eq, List.map_range_getD]

end Airbender.Compiler
