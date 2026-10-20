import Slop.ByteTables
import Slop.Arithmetic.Bytes
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification

/-- The native sign query extends its input byte, including the zero case. -/
theorem binary_sign_lookup {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)}
    (h : (shiftBinopLookup entry).Contains env)
    (selected : entry[9].eval env = 3) :
    (entry[0].eval env).val < 256 ∧
      (entry[1].eval env).val = if (entry[0].eval env).val < 128 then 0 else 255 := by
  obtain ⟨i, tagged, column⟩ := tagged_lookup_row hp h 3 (by decide) selected
  have interval : 1 ≤ i.val ∧ i.val < 257 := by
    unfold shiftBinopRow at tagged
    dsimp only at tagged
    split_ifs at tagged <;> simp [binaryByteRow] at tagged <;> omega
  have shape : shiftBinopRow i =
      #v[i.val - 1, if i.val - 1 < 128 then 0 else 255, 0, 0, 0, 0, 0, 0, 0, 3] := by
    simp [shiftBinopRow, show i.val ≠ 0 by omega, interval.2]
  have a := column 0 (by decide)
  have b := column 1 (by decide)
  rw [shape] at a b
  change entry[0].eval env = ((i.val - 1 : Nat) : ZMod p) at a
  change entry[1].eval env = ((if i.val - 1 < 128 then 0 else 255 : Nat) : ZMod p) at b
  have av : (entry[0].eval env).val = i.val - 1 := by
    rw [a, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [av, b, ZMod.val_natCast]
  refine ⟨by omega, ?_⟩
  split_ifs <;> rw [Nat.mod_eq_of_lt (by omega)]

private theorem truncation_rows (i : Fin 524545)
    (selected : (shiftBinopRow i)[9] = 8) :
    (shiftBinopRow i)[0] < 256 ∧ (shiftBinopRow i)[1] < 256 ∧
      (shiftBinopRow i)[2] = (shiftBinopRow i)[0] % 32 := by
  have interval : 196865 ≤ i.val ∧ i.val < 262401 := by
    unfold shiftBinopRow at selected
    dsimp only at selected
    split_ifs at selected <;> simp [binaryByteRow] at selected
    all_goals omega
  simp only [shiftBinopRow, show i.val ≠ 0 by omega, ite_false,
    show ¬ i.val < 257 by omega, show ¬ i.val < 65793 by omega,
    show ¬ i.val < 131329 by omega, show ¬ i.val < 196865 by omega,
    interval.2, ite_true]
  have tuple (a b : Fin 256) :
      (#v[a.val, b.val, a.val % 32, 0, 0, 0, 0, 0, 0, 8] : Vector Nat 10)[0] < 256 ∧
      (#v[a.val, b.val, a.val % 32, 0, 0, 0, 0, 0, 0, 8] : Vector Nat 10)[1] < 256 ∧
      (#v[a.val, b.val, a.val % 32, 0, 0, 0, 0, 0, 0, 8] : Vector Nat 10)[2] =
        (#v[a.val, b.val, a.val % 32, 0, 0, 0, 0, 0, 0, 8] : Vector Nat 10)[0] % 32 :=
    ⟨a.isLt, b.isLt, rfl⟩
  apply tuple

/-- The native truncation query enforces the low five bits of its first byte. -/
theorem truncation_lookup {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)}
    (h : (shiftBinopLookup entry).Contains env)
    (selected : entry[9].eval env = 8) :
    (entry[0].eval env).val < 256 ∧ (entry[1].eval env).val < 256 ∧
      (entry[2].eval env).val = (entry[0].eval env).val % 32 := by
  obtain ⟨i, tagged, column⟩ := tagged_lookup_row hp h 8 (by decide) selected
  obtain ⟨a, b, c⟩ := truncation_rows i tagged
  have cb : (shiftBinopRow i)[2] < 256 := by rw [c]; omega
  have values (j : Nat) (hj : j < 10) (bound : (shiftBinopRow i)[j] < 256) :
      (entry[j].eval env).val = (shiftBinopRow i)[j] := by
    rw [column j hj, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [values 0 (by decide) a, values 1 (by decide) b, values 2 (by decide) cb]
  exact ⟨a, b, c⟩

private theorem shift_rows (i : Fin 524545) (selected : (shiftBinopRow i)[9] = 9) :
    (∀ j : Nat, ∀ hj : j < 10, (shiftBinopRow i)[j] < 256) ∧
    (shiftBinopRow i)[0] < 4 ∧ (shiftBinopRow i)[2] < 32 ∧
    (shiftBinopRow i)[3] < 8 ∧
    ∀ j : Fin 4, (shiftBinopRow i)[4 + j.val] =
      ((shiftByteContribution (shiftBinopRow i)[0] (shiftBinopRow i)[1]
        (shiftBinopRow i)[2] (shiftBinopRow i)[3]).extractLsb' (8 * j.val) 8).toNat := by
  have lower : 262401 ≤ i.val := by
    unfold shiftBinopRow at selected
    dsimp only at selected
    split_ifs at selected <;> simp [binaryByteRow] at selected
    all_goals omega
  have size := i.isLt
  have shape : shiftBinopRow i =
      let key := i.val - 262401
      let output := (shiftByteContribution (key / 65536) (key / 256 % 256)
        (key / 8 % 32) (key % 8)).toNat
      #v[key / 65536, key / 256 % 256, key / 8 % 32, key % 8,
        output % 256, output / 256 % 256, output / 65536 % 256,
        output / 16777216 % 256, 0, 9] := by
    simp [shiftBinopRow, show i.val ≠ 0 by omega, show ¬ i.val < 257 by omega,
      show ¬ i.val < 65793 by omega, show ¬ i.val < 131329 by omega,
      show ¬ i.val < 196865 by omega, show ¬ i.val < 262401 by omega]
  rw [shape]
  refine ⟨?_, by dsimp; omega, by dsimp; omega, by dsimp; omega, ?_⟩
  · intro j hj
    interval_cases j <;> dsimp <;> omega
  · intro j
    fin_cases j <;>
      simp [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

/-- Four canonical output bytes are forced by the selected native shift row.
    Table provenance remains the same explicit external binding as for binops. -/
theorem shift_lookup {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {entry : Vector (Expression (ZMod p)) 10} {env : Environment (ZMod p)}
    (h : (shiftBinopLookup entry).Contains env)
    (selected : entry[9].eval env = 9) :
    (entry[0].eval env).val < 4 ∧ (entry[1].eval env).val < 256 ∧
    (entry[2].eval env).val < 32 ∧ (entry[3].eval env).val < 8 ∧
    ∀ j : Fin 4, (entry[4 + j.val].eval env).val =
      ((shiftByteContribution (entry[0].eval env).val (entry[1].eval env).val
        (entry[2].eval env).val (entry[3].eval env).val).extractLsb'
          (8 * j.val) 8).toNat := by
  obtain ⟨i, tagged, column⟩ := tagged_lookup_row hp h 9 (by decide) selected
  obtain ⟨bounds, position, amount, operation, output⟩ := shift_rows i tagged
  have values (j : Nat) (hj : j < 10) :
      (entry[j].eval env).val = (shiftBinopRow i)[j] := by
    rw [column j hj, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := bounds j hj; omega)]
  rw [values 0 (by decide), values 1 (by decide), values 2 (by decide), values 3 (by decide)]
  refine ⟨position, bounds 1 (by decide), amount, operation, ?_⟩
  intro j
  rw [values (4 + j.val) (by have := j.isLt; omega)]
  exact output j

end Airbender.Verification
