import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.Arithmetic
open scoped BigOperators
set_option warningAsError true

def limbSum (radix length : Nat) (limbs : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.range length, radix ^ i * limbs i

/-- A finite carry recurrence composes into an exact multi-limb equation. -/
theorem carry_chain {radix length : Nat} {left right result carry : Nat → Nat}
    (steps : ∀ i < length, left i + right i + carry i = result i + radix * carry (i + 1)) :
    limbSum radix length left + limbSum radix length right + carry 0 =
      limbSum radix length result + radix ^ length * carry length := by
  induction length with
  | zero => simp [limbSum]
  | succ n ih =>
    have initial := ih (fun i hi => steps i (by omega))
    have last := congrArg (fun value => radix ^ n * value) (steps n (by omega))
    simp only [limbSum, Finset.sum_range_succ, pow_succ] at *
    ring_nf at initial last ⊢
    omega

end Airbender.Arithmetic
