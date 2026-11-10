module
public import Human.Helpers.Core.BabyBearPrime

/-! The claims' field premises pin BabyBear: an inverse premise `(-a : ZMod p) * b = 1` (or `b * (-a) = 1`) with
`a * b = babyBearModulus - 1` says `p ∣ babyBearModulus`, so a prime `p` is `babyBearModulus`. `babybear_instance h`
proves a claim stated at BabyBear from a proof `h` of the same statement for every prime `p` with those premises
(the converse was checked once, for every restated claim, in test/Checks/Restatements.lean, in git history up to d8cb7e2d8). -/

@[expose] public section

/-- Close a BabyBear claim from a proof `h` of its generic-prime form `∀ {p} [Fact p.Prime], premises → …`:
    instantiate `p := babyBearModulus` and discharge its one to five numeric premises by `decide`. -/
macro "babybear_instance " h:term : tactic => `(tactic| first
  | exact $h (p := Airbender.babyBearModulus) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide) (by decide) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide) (by decide) (by decide) (by decide))
