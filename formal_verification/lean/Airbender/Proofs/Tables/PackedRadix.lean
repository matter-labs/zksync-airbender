import Airbender.Proofs.Tables.PackedBytes

namespace Airbender.Setup.Proofs.PackedRadix
set_option warningAsError true

/-- Read one bounded digit from any fixed-base packed payload. -/
theorem extractDigitBase (standard : Nat) (digits : List Nat) (index : Nat)
    (positive : 0 < standard)
    (bounded : ∀ value ∈ digits, value < standard) (within : index < digits.length) :
    (Nat.ofDigits standard digits / standard ^ index) % standard = digits[index] := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index positive digits bounded,
    List.drop_eq_getElem_cons within]
  simp [Nat.ofDigits, Nat.mod_eq_of_lt (bounded _ (List.getElem_mem within))]

end Airbender.Setup.Proofs.PackedRadix
