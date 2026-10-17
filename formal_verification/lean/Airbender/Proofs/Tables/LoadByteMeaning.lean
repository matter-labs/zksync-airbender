import Airbender.Proofs.Tables.ReferenceSubwordRows

namespace Airbender.Verification.SubwordFixed
set_option warningAsError true
set_option Elab.async false

def byteValue (n : Nat) : Nat := if n < 131072 then n % 256 else n / 256 % 256
def byteNegative (n : Nat) : Prop := n / 65536 % 2 = 1 ∧ 128 ≤ byteValue n
instance (n : Nat) : Decidable (byteNegative n) := inferInstanceAs (Decidable (_ ∧ _))
def byteLow (n : Nat) : Nat := byteValue n + if byteNegative n then 65280 else 0
def byteHigh (n : Nat) : Nat := if byteNegative n then 65535 else 0

theorem byte_meaning (n : Nat) (bound : n < 262144) :
    subwordLoadLimbs true n = (byteLow n, byteHigh n) := by
  have value : n % 65536 / (if n / 131072 % 2 = 1 then 256 else 1) % 256 = byteValue n := by
    by_cases low : n < 131072
    · have selector : n / 131072 % 2 = 0 := by omega
      simp only [selector, Nat.zero_ne_one, if_false, Nat.div_one, byteValue, if_pos low]
      omega
    · have selector : n / 131072 % 2 = 1 := by omega
      simp only [selector, if_true, byteValue, if_neg low]
      omega
  simp [subwordLoadLimbs, byteLow, byteHigh, byteNegative, value]

end Airbender.Verification.SubwordFixed
