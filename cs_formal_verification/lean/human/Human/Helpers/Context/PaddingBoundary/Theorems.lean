module
public import Human.Helpers.Context.PaddingBoundary.Model
public import Human.Helpers.Core.BabyBearPrime

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
/-- The native Boolean contribution premise holds for a participating row. -/
def ContributionSatisfiableClaim : Prop :=
  ∃ execute : ZMod babyBearModulus, execute = 1 ∧ (execute = 0 ∨ execute = 1)
end Airbender.PaddingBoundary
