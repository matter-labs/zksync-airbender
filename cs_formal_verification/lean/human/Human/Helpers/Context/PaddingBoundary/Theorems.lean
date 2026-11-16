module
public import Human.Helpers.Context.PaddingBoundary.Model
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Context.Registries.Pooled

@[expose] public section
namespace Airbender.PaddingBoundary

/-- Boolean row contributions equal the native scalar mask for every encoded tuple. -/
def ContributionSoundnessClaim : Prop :=
  ∀ (execute : ZMod babyBearModulus), execute = 0 ∨ execute = 1 →
    ∀ (encode : Nat → ZMod babyBearModulus) (value : Nat),
      evaluate encode (contribution execute value) = mask execute (encode value)

/-- The contribution mask applies to each row product. -/
def ProductSoundnessClaim : Prop :=
  ∀ (execute : ZMod babyBearModulus), execute = 0 ∨ execute = 1 →
    ∀ (encode : Nat → ZMod babyBearModulus) (values : List Nat),
      ((values.map (contribution execute)).map (evaluate encode)).prod = mask execute (values.map encode).prod

/-- Optional tuple closure projects an accepted padded layout to its participating rows. -/
def ProjectionClaim : Prop :=
  ∀ {Kind : Type} [Trace.CircuitLayout Kind] (trace : Trace.Data babyBearModulus Kind),
    AcceptedLayout trace → Trace.Accepted (active trace)

end Airbender.PaddingBoundary

namespace Airbender.PaddingBoundary
/-- A participating row supplies the Boolean selector, encoding and value of the contribution claim. -/
def ContributionSatisfiableClaim : Prop :=
  ∃ (execute : ZMod babyBearModulus) (encode : Nat → ZMod babyBearModulus) (value : Nat),
    (execute = 0 ∨ execute = 1) ∧ execute = 1 ∧ encode value ≠ 0

/-- A nonempty row product supplies the Boolean selector, encoding and values of the product claim. -/
def ProductSatisfiableClaim : Prop :=
  ∃ (execute : ZMod babyBearModulus) (encode : Nat → ZMod babyBearModulus) (values : List Nat),
    (execute = 0 ∨ execute = 1) ∧ execute = 1 ∧ values ≠ [] ∧ (values.map encode).prod ≠ 0

/-- An accepted padded layout supplies every premise of the projection claim. -/
def ProjectionSatisfiableClaim : Prop :=
  ∃ (trace : Trace.PooledTrace babyBearModulus), AcceptedLayout trace
end Airbender.PaddingBoundary
