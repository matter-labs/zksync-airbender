module
public import Slop.KeccakSplit.Setup.Chi5.Spec
public import Slop.KeccakSplit.Setup.Facts

@[expose] public section

/- Meaning of the chi5 formula rows, by tag, over BabyBear. -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-- The row formulas, one per column. -/
def formulaRow (n : Nat) : Vector Nat 11 :=
  #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n, spec6 n, spec7 n, spec8 n, spec9 n,
    spec10 n]

theorem get0 (n : Nat) : (formulaRow n)[0] = spec0 n := by rfl
theorem get1 (n : Nat) : (formulaRow n)[1] = spec1 n := by rfl
theorem get2 (n : Nat) : (formulaRow n)[2] = spec2 n := by rfl
theorem get3 (n : Nat) : (formulaRow n)[3] = spec3 n := by rfl
theorem get4 (n : Nat) : (formulaRow n)[4] = spec4 n := by rfl
theorem get5 (n : Nat) : (formulaRow n)[5] = spec5 n := by rfl
theorem get6 (n : Nat) : (formulaRow n)[6] = spec6 n := by rfl
theorem get7 (n : Nat) : (formulaRow n)[7] = spec7 n := by rfl
theorem get8 (n : Nat) : (formulaRow n)[8] = spec8 n := by rfl
theorem get9 (n : Nat) : (formulaRow n)[9] = spec9 n := by rfl
theorem get10 (n : Nat) : (formulaRow n)[10] = spec10 n := by rfl

/-- A field row that is the cast of a formula row of the trace. -/
def IsFormulaRow (row : Vector (ZMod babyBearModulus) 11) : Prop :=
  ∃ n < 4194304, row = (formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus))

private theorem tag_of {n t : Nat} (ht : t ≤ 66)
    (h : ((formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus)))[10] =
      (t : ZMod babyBearModulus)) : spec10 n = t := by
  have le : spec10 n ≤ 66 := by unfold spec10; split_ifs <;> omega
  rw [Vector.getElem_map, get10] at h
  exact cast_inj (by omega) (by omega) h

theorem chiOut_lt (m k : Nat) : chiOut m k < 16 :=
  Nat.xor_lt_two_pow (n := 4) (nib_lt _ _) (Nat.and_lt_two_pow _ (nib_lt _ _))

/-- Tag 65: chi on four-bit slices of a plane. -/
theorem chi_facts {row : Vector (ZMod babyBearModulus) 11} (h : IsFormulaRow row)
    (tag : row[10] = 65) :
    (row[0].val < 16 ∧ row[1].val < 16 ∧ row[2].val < 16 ∧ row[3].val < 16 ∧ row[4].val < 16) ∧
      (row[5].val < 16 ∧ row[6].val < 16 ∧ row[7].val < 16 ∧ row[8].val < 16 ∧
        row[9].val < 16) ∧
      row[5].val = row[0].val ^^^ ((15 ^^^ row[1].val) &&& row[2].val) ∧
      row[6].val = row[1].val ^^^ ((15 ^^^ row[2].val) &&& row[3].val) ∧
      row[7].val = row[2].val ^^^ ((15 ^^^ row[3].val) &&& row[4].val) ∧
      row[8].val = row[3].val ^^^ ((15 ^^^ row[4].val) &&& row[0].val) ∧
      row[9].val = row[4].val ^^^ ((15 ^^^ row[0].val) &&& row[1].val) := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 65) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : n < 1048576 := by unfold spec10 at t; split_ifs at t <;> omega
  have e0 : spec0 n = nib n 0 := by unfold spec0; region
  have e1 : spec1 n = nib n 1 := by unfold spec1; region
  have e2 : spec2 n = nib n 2 := by unfold spec2; region
  have e3 : spec3 n = nib n 3 := by unfold spec3; region
  have e4 : spec4 n = nib n 4 := by unfold spec4; region
  have e5 : spec5 n = chiOut n 0 := by unfold spec5; region
  have e6 : spec6 n = chiOut n 1 := by unfold spec6; region
  have e7 : spec7 n = chiOut n 2 := by unfold spec7; region
  have e8 : spec8 n = chiOut n 3 := by unfold spec8; region
  have e9 : spec9 n = chiOut n 4 := by unfold spec9; region
  have vn (k : Nat) : ((nib n k : Nat) : ZMod babyBearModulus).val = nib n k :=
    val_cast (by have := nib_lt n k; omega)
  have vc (k : Nat) : ((chiOut n k : Nat) : ZMod babyBearModulus).val = chiOut n k :=
    val_cast (by have := chiOut_lt n k; omega)
  simp only [Vector.getElem_map, get0, get1, get2, get3, get4, get5, get6, get7, get8, get9,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, vn, vc]
  exact ⟨⟨nib_lt _ _, nib_lt _ _, nib_lt _ _, nib_lt _ _, nib_lt _ _⟩,
    ⟨chiOut_lt _ _, chiOut_lt _ _, chiOut_lt _ _, chiOut_lt _ _, chiOut_lt _ _⟩,
    rfl, rfl, rfl, rfl, rfl⟩

private theorem control_region {n : Nat}
    (tag : ((formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus)))[10] = 66) :
    1048576 ≤ n ∧ n < 1048697 := by
  have t := tag_of (t := 66) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  unfold spec10 at t; split_ifs at t <;> omega

/-- Tag 66: the execute column is boolean. -/
theorem control_execute {row : Vector (ZMod babyBearModulus) 11} (h : IsFormulaRow row)
    (tag : row[10] = 66) : row[1] = 0 ∨ row[1] = 1 := by
  obtain ⟨n, -, rfl⟩ := h
  have r := control_region tag
  rw [Vector.getElem_map, get1]
  by_cases z : n = 1048576
  · left
    have : spec1 n = 0 := by simp (disch := omega) only [spec1, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
    rw [this, Nat.cast_zero]
  · right
    have : spec1 n = 1 := by simp (disch := omega) only [spec1, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
    rw [this, Nat.cast_one]

/-- Tag 66: the plane column is below five (the zero key included). -/
theorem control_plane {row : Vector (ZMod babyBearModulus) 11} (h : IsFormulaRow row)
    (tag : row[10] = 66) : row[8].val < 5 := by
  obtain ⟨n, -, rfl⟩ := h
  have r := control_region tag
  have e8 : spec8 n < 5 := by simp only [spec8, ctl]; split_ifs <;> omega
  rw [Vector.getElem_map, get8, val_cast (by omega)]
  exact e8

/-- Tag 66, executed: the controller row of a chi call. -/
theorem control_facts {row : Vector (ZMod babyBearModulus) 11} (h : IsFormulaRow row)
    (tag : row[10] = 66) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .chi5 ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (row[3] = ((Call.slots index)[0].val : ZMod babyBearModulus) ∧
        row[4] = ((Call.slots index)[1].val : ZMod babyBearModulus) ∧
        row[5] = ((Call.slots index)[2].val : ZMod babyBearModulus) ∧
        row[6] = ((Call.slots index)[3].val : ZMod babyBearModulus) ∧
        row[7] = ((Call.slots index)[4].val : ZMod babyBearModulus)) ∧
      row[8] = ((index.val % 5 : Nat) : ZMod babyBearModulus) := by
  obtain ⟨n, -, rfl⟩ := h
  have r := control_region tag
  have nz : n ≠ 1048576 := by
    rintro rfl
    rw [Vector.getElem_map, get1] at active
    have : spec1 1048576 = 0 := by simp (disch := omega) only [spec1, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
    rw [this, Nat.cast_zero] at active
    exact zero_ne_one active
  have j : callAt (n - 1048576) < 361 := callIndex_lt (by omega) (by omega) (by omega)
  have e0 : spec0 n = controlAt (callAt (n - 1048576)) := by
    simp (disch := omega) only [spec0, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e2 : spec2 n = bump (controlAt (callAt (n - 1048576))) := by
    simp (disch := omega) only [spec2, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e3 : spec3 n = slotNat (callAt (n - 1048576)) 0 := by
    simp (disch := omega) only [spec3, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e4 : spec4 n = slotNat (callAt (n - 1048576)) 1 := by
    simp (disch := omega) only [spec4, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e5 : spec5 n = slotNat (callAt (n - 1048576)) 2 := by
    simp (disch := omega) only [spec5, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e6 : spec6 n = slotNat (callAt (n - 1048576)) 3 := by
    simp (disch := omega) only [spec6, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e7 : spec7 n = slotNat (callAt (n - 1048576)) 4 := by
    simp (disch := omega) only [spec7, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e8 : spec8 n = callAt (n - 1048576) % 5 := by
    simp (disch := omega) only [spec8, ctl, ite_eq_left, ite_eq_right, ite_true, ite_false]
  refine ⟨⟨callAt (n - 1048576), j⟩, chi5_kindAt _, ?_, ?_, ?_, ?_⟩
  · rw [Vector.getElem_map, get0, e0]
  · rw [Vector.getElem_map, get2, e2]
  · simp only [Vector.getElem_map, get3, get4, get5, get6, get7, e3, e4, e5, e6, e7,
      slotNat_eq j (by omega : 0 < 7), slotNat_eq j (by omega : 1 < 7),
      slotNat_eq j (by omega : 2 < 7), slotNat_eq j (by omega : 3 < 7),
      slotNat_eq j (by omega : 4 < 7)]
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  · rw [Vector.getElem_map, get8, e8]

end Airbender.Keccak.Split.Chi5.SetupProofs
