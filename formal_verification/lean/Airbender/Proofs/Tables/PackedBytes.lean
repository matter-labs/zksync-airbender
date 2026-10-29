import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Bitwise

namespace Airbender.Setup.Proofs.PackedBytes

set_option warningAsError true

/-- Compare a fixed number of packed rows with a public expected-row function.
The expected function is separate from the importer and can be reviewed once. -/
def checkRows (actual : Array Nat) (length : Nat) (expected : Nat → Nat) : Bool :=
  actual.size == length &&
    (List.finRange length).all (fun row => actual[row.val]? == some (expected row.val))

/-- A successful finite check supplies every row equality. This theorem is
independent of any capture, importer or chosen expected-row formula. -/
theorem checkRows_sound (actual : Array Nat) (length : Nat) (expected : Nat → Nat)
    (h : checkRows actual length expected = true) (row : Fin length) :
    actual[row.val]? = some (expected row.val) := by
  simp only [checkRows, Bool.and_eq_true] at h
  have hrow := (List.all_eq_true.mp h.2) row (List.mem_finRange row)
  simpa using hrow

/-- Reading a checked base-256 digit recovers the corresponding byte. -/
theorem extractDigit (digits : List Nat) (index : Nat)
    (bounded : ∀ digit ∈ digits, digit < 256) (within : index < digits.length) :
    (Nat.ofDigits 256 digits / 256 ^ index) % 256 = digits[index] := by
  calc
    (Nat.ofDigits 256 digits / 256 ^ index) % 256 =
        Nat.ofDigits 256 (digits.drop index) % 256 := by
      rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index (by omega) digits bounded]
    _ = Nat.ofDigits 256 (digits[index] :: digits.drop (index + 1)) % 256 := by
      rw [List.drop_eq_getElem_cons within]
    _ = digits[index] := by
      simp [Nat.ofDigits, Nat.mod_eq_of_lt
        (bounded digits[index] (List.getElem_mem within))]

/-- A base-256 byte of a bitwise AND is the AND of the corresponding bytes. -/
theorem extractAnd (a b index : Nat) :
    ((a &&& b) / 256 ^ index) % 256 =
      ((a / 256 ^ index) % 256) &&& ((b / 256 ^ index) % 256) := by
  have hpow : 256 ^ index = 2 ^ (8 * index) := by
    rw [pow_mul]
    norm_num
  rw [hpow, Nat.and_div_two_pow]
  simpa only [show (2 : Nat) ^ 8 = 256 by norm_num] using
    (Nat.and_mod_two_pow (a := a / 2 ^ (8 * index))
      (b := b / 2 ^ (8 * index)) (n := 8))

end Airbender.Setup.Proofs.PackedBytes
