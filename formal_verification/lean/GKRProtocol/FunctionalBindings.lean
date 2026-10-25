import GKRProtocol.Functional
import GKRProtocol.NativeProduct

namespace Airbender.Compiler
set_option warningAsError true

def RExpression.sub (left right : RExpression) : RExpression := .add left (.neg right)

theorem TypedAssignment.value_from_function [CommRing R] (typing : ConsumerTyping)
    (hom : Source.BaseField →+* R) (baseValue : GKRAddress → Source.BaseField)
    (values : GKRAddress → R)
    (base : ∀ address, typing.compatible (address, .base) = true → values address = hom (baseValue address)) :
    (TypedAssignment.mk baseValue values).value typing hom = values := by
  funext address
  change (if typing.compatible (address, .base) then hom (baseValue address) else values address) = values address
  split_ifs with role
  · exact (base address role).symm
  · rfl

def LookupWeight.functional : LookupWeight → RExpression
  | .one => .coefficient (.natural 1)
  | .column address => .input address
  | .negativeMultiplicity address => .neg (.input address)

def AffineDefinition.functional (definition : AffineDefinition) : FunctionalStep :=
  [(definition.output, .affine definition.program)]

theorem AffineDefinition.functional_sound [CommRing R] (definition : AffineDefinition)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (values : GKRAddress → R) (holds : definition.functional.Holds hom challenges gamma values) :
    definition.Holds hom challenges values :=
  holds _ (List.mem_cons_self)

def RationalPorts.assignments (ports : RationalPorts) (numerator denominator : RExpression) : FunctionalStep :=
  [(ports.numerator, numerator), (ports.denominator, denominator)]

theorem RationalPorts.assignments_sound [CommRing R] (ports : RationalPorts) (numerator denominator : RExpression)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (values : GKRAddress → R)
    (holds : (ports.assignments numerator denominator).Holds hom challenges gamma values) :
    ports.value values = ⟨numerator.value hom challenges gamma values, denominator.value hom challenges gamma values⟩ := by
  apply congrArg₂ RationalPair.mk
  · exact holds _ List.mem_cons_self
  · exact holds _ (List.mem_cons_of_mem _ List.mem_cons_self)

def NativeProductGate.functional : NativeProductGate → FunctionalStep
  | .single output input => [(output, .affine input)]
  | .pair output left right => [(output, .mul (.affine left) (.affine right))]
  | .mul output left right => [(output, .mul (.input left) (.input right))]
  | .mask output input predicate =>
      [(output, .add (.mul (RExpression.sub (.input input) (.coefficient (.natural 1)))
        (.input predicate)) (.coefficient (.natural 1)))]
  | .copy output input => [(output, .input input)]

theorem NativeProductGate.functional_sound [CommRing R] (gate : NativeProductGate)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (values : GKRAddress → R)
    (holds : gate.functional.Holds hom challenges gamma values) : gate.Holds hom challenges values := by
  cases gate <;>
    simpa only [functional, FunctionalStep.Holds, List.mem_singleton, forall_eq, RExpression.value,
      RExpression.sub, CacheCoefficient.value, Nat.cast_one, map_one, NativeProductGate.Holds, maskProduct, sub_eq_add_neg] using holds

def NativeLookupGate.functional : NativeLookupGate → FunctionalStep
  | .pair output left right =>
      let l : RExpression := .add (.affine left) .lookupGamma
      let r : RExpression := .add (.affine right) .lookupGamma
      output.assignments (.add l r) (.mul l r)
  | .setup output mask input multiplicity table =>
      let i : RExpression := .add (.affine input) .lookupGamma
      let t : RExpression := .add (.affine table) .lookupGamma
      output.assignments (RExpression.sub (.mul mask.functional t) (.mul (.input multiplicity) i)) (.mul i t)
  | .add output left right =>
      output.assignments
        (.add (.mul (.input left.numerator) (.input right.denominator))
          (.mul (.input left.denominator) (.input right.numerator)))
        (.mul (.input left.denominator) (.input right.denominator))
  | .extend output input remainder =>
      let denominator : RExpression := .add (.affine remainder) .lookupGamma
      output.assignments (.add (.mul (.input input.numerator) denominator) (.input input.denominator))
        (.mul (.input input.denominator) denominator)
  | .copy output input => [(output, .input input)]

theorem NativeLookupGate.functional_sound [CommRing R] (gate : NativeLookupGate)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (values : GKRAddress → R)
    (holds : gate.functional.Holds hom challenges gamma values) : gate.Holds hom challenges gamma values := by
  cases gate with
  | copy output input =>
      exact holds _ List.mem_cons_self
  | pair output left right =>
      exact output.assignments_sound _ _ hom challenges gamma values holds
  | add output left right =>
      exact output.assignments_sound _ _ hom challenges gamma values holds
  | extend output input remainder =>
      exact output.assignments_sound _ _ hom challenges gamma values holds
  | setup output mask input multiplicity table =>
      have result := output.assignments_sound _ _ hom challenges gamma values holds
      cases mask <;>
        simpa only [NativeLookupGate.Holds, lookupMinusSetup, LookupWeight.value, LookupWeight.functional,
          RExpression.value, RExpression.sub, CacheCoefficient.value, Nat.cast_one, map_one, sub_eq_add_neg] using result

end Airbender.Compiler
