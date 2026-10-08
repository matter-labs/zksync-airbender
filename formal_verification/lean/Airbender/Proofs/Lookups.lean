import Airbender.Review.Lookups

namespace Airbender.Verification

theorem pair_value_of_row {p bound : Nat} [Fact p.Prime]
    {value : Nat → Nat} {key result : ZMod p} (hp : bound ≤ p)
    (h : ∃ i : Fin bound, (key, result) = ((i.val : ZMod p), (value i.val : ZMod p))) :
    key.val < bound ∧ result = (value key.val : ZMod p) := by
  obtain ⟨i, row⟩ := h
  obtain ⟨hk, hr⟩ := Prod.mk.inj row
  have hv : key.val = i.val := by
    rw [hk, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hp)]
  exact ⟨hv ▸ i.isLt, by simpa only [hv] using hr⟩

theorem regIsZero_value {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    {key value : Expression (ZMod p)} {env : Environment (ZMod p)}
    (h : (pairLookup regIsZeroTable key value).Contains env) :
    (key.eval env).val < 131072 ∧
      value.eval env = if (key.eval env).val = 0 then 1 else 0 := by
  have hs := (pairLookup regIsZeroTable key value).table.imply_soundness _ _ h
  have rows := (Lookup.soundess_def regIsZeroTable env (key, value)).mp hs
  with_unfolding_all change ∃ i : Fin 131072, (key.eval env, value.eval env) =
    ((i.val : ZMod p), ((if i.val = 0 then 1 else 0 : Nat) : ZMod p)) at rows
  have result := pair_value_of_row (value := fun n => if n = 0 then 1 else 0) hp rows
  simpa using result

theorem u16Sign_value {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {key value : Expression (ZMod p)} {env : Environment (ZMod p)}
    (h : (pairLookup u16SignTable key value).Contains env) :
    (key.eval env).val < 65536 ∧
      value.eval env = (((key.eval env).val / 32768 : Nat) : ZMod p) := by
  have hs := (pairLookup u16SignTable key value).table.imply_soundness _ _ h
  have rows := (Lookup.soundess_def u16SignTable env (key, value)).mp hs
  with_unfolding_all change ∃ i : Fin 65536, (key.eval env, value.eval env) =
    ((i.val : ZMod p), ((i.val / 32768 : Nat) : ZMod p)) at rows
  exact pair_value_of_row (value := fun n => n / 32768) hp rows

theorem conditional_value {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {key value : Expression (ZMod p)} {env : Environment (ZMod p)}
    (h : (pairLookup conditionalTable key value).Contains env) :
    (key.eval env).val < 4194304 ∧
      value.eval env = (conditionalValue (key.eval env).val : ZMod p) := by
  have hs := (pairLookup conditionalTable key value).table.imply_soundness _ _ h
  have rows := (Lookup.soundess_def conditionalTable env (key, value)).mp hs
  with_unfolding_all change ∃ i : Fin 4194304, (key.eval env, value.eval env) =
    ((i.val : ZMod p), (conditionalValue i.val : ZMod p)) at rows
  exact pair_value_of_row hp rows

theorem u16LowByte_value {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {key value : Expression (ZMod p)} {env : Environment (ZMod p)}
    (h : (pairLookup u16LowByteTable key value).Contains env) :
    (key.eval env).val < 65536 ∧
      value.eval env = (((key.eval env).val % 256 : Nat) : ZMod p) := by
  have hs := (pairLookup u16LowByteTable key value).table.imply_soundness _ _ h
  have rows := (Lookup.soundess_def u16LowByteTable env (key, value)).mp hs
  with_unfolding_all change ∃ i : Fin 65536, (key.eval env, value.eval env) =
    ((i.val : ZMod p), ((i.val % 256 : Nat) : ZMod p)) at rows
  exact pair_value_of_row (value := fun n => n % 256) hp rows

theorem jumpCleanup_value {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {key bit1 cleaned : Expression (ZMod p)} {env : Environment (ZMod p)}
    (h : (jumpCleanup key bit1 cleaned).Contains env) :
    (key.eval env).val < 65536 ∧
      bit1.eval env = (((key.eval env).val / 2 % 2 : Nat) : ZMod p) ∧
      cleaned.eval env = (((key.eval env).val - (key.eval env).val % 4 : Nat) : ZMod p) := by
  have hs := (jumpCleanup key bit1 cleaned).table.imply_soundness _ _ h
  have rows := (Lookup.soundess_def jumpCleanupTable env (key, bit1, cleaned)).mp hs
  with_unfolding_all change ∃ i : Fin 65536, (key.eval env, bit1.eval env, cleaned.eval env) =
    ((i.val : ZMod p), ((i.val / 2 % 2 : Nat) : ZMod p), ((i.val - i.val % 4 : Nat) : ZMod p)) at rows
  obtain ⟨i, row⟩ := rows
  obtain ⟨hk, hr⟩ := Prod.mk.inj row
  have hv : (key.eval env).val = i.val := by
    rw [hk, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hp)]
  exact ⟨hv ▸ i.isLt, by simpa only [hv] using (Prod.mk.inj hr).1,
    by simpa only [hv] using (Prod.mk.inj hr).2⟩

end Airbender.Verification
