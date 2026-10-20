import Slop.Arithmetic.Lemmas

namespace Airbender.Arithmetic
open scoped BigOperators
set_option warningAsError true

/-- A canonical nonnegative sum of one selects a unique field entry. The sum
    must already have been lifted out of the field, excluding modular wrap. -/
theorem field_selection {p n : Nat} [Fact p.Prime] {bits : Fin n → ZMod p}
    (total : (∑ i : Fin n, (bits i).val) = 1) :
    ∃ selected : Fin n, ∀ i : Fin n, bits i = if i = selected then 1 else 0 := by
  have positive : 0 < ∑ i : Fin n, (bits i).val := by omega
  obtain ⟨selected, _, nonzero⟩ := Finset.sum_pos_iff.mp positive
  have below := Finset.single_le_sum (f := fun i => (bits i).val)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ selected)
  have one : (bits selected).val = 1 := by omega
  refine ⟨selected, ?_⟩
  intro i
  have cast := ZMod.natCast_zmod_val (bits i)
  split_ifs with same
  · subst i
    simpa only [one, Nat.cast_one] using cast.symm
  · have zero := sum_le_one_exclusive (f := fun j => (bits j).val) (by omega) selected one i same
    simpa only [zero, Nat.cast_zero] using cast.symm

end Airbender.Arithmetic
