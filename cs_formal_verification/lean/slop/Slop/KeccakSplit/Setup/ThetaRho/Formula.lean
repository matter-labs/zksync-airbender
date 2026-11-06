import Slop.KeccakSplit.Setup.ThetaRho.Spec
import Slop.KeccakSplit.Setup.Facts

/- Meaning of the theta/rho formula rows, by tag, over BabyBear. -/

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-- The row formulas, one per column. -/
def formulaRow (n : Nat) : Vector Nat 9 :=
  #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n, spec6 n, spec7 n, spec8 n]

theorem get0 (n : Nat) : (formulaRow n)[0] = spec0 n := rfl
theorem get1 (n : Nat) : (formulaRow n)[1] = spec1 n := rfl
theorem get2 (n : Nat) : (formulaRow n)[2] = spec2 n := rfl
theorem get3 (n : Nat) : (formulaRow n)[3] = spec3 n := rfl
theorem get4 (n : Nat) : (formulaRow n)[4] = spec4 n := rfl
theorem get5 (n : Nat) : (formulaRow n)[5] = spec5 n := rfl
theorem get6 (n : Nat) : (formulaRow n)[6] = spec6 n := rfl
theorem get7 (n : Nat) : (formulaRow n)[7] = spec7 n := rfl
theorem get8 (n : Nat) : (formulaRow n)[8] = spec8 n := rfl

/-- A field row that is the cast of a formula row of the trace. -/
def IsFormulaRow (row : Vector (ZMod babyBearModulus) 9) : Prop :=
  ∃ n < 4194304, row = (formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus))

private theorem tag_of {n t : Nat} (ht : t ≤ 60)
    (h : ((formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus)))[8] =
      (t : ZMod babyBearModulus)) : spec8 n = t := by
  have le : spec8 n ≤ 60 := by unfold spec8; split_ifs <;> omega
  rw [Vector.getElem_map, get8] at h
  exact cast_inj (by omega) (by omega) h

/-- Tag 4: byte XOR. -/
theorem xor_facts {row : Vector (ZMod babyBearModulus) 9} (h : IsFormulaRow row)
    (tag : row[8] = 4) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ row[1].val ∧
      row[3] = 0 ∧ row[4] = 0 ∧ row[5] = 0 ∧ row[6] = 0 ∧ row[7] = 0 := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 4) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : n < 65536 := by unfold spec8 at t; split_ifs at t <;> omega
  have e0 : spec0 n = n / 256 := by simp (disch := omega) only [spec0, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e1 : spec1 n = n % 256 := by simp (disch := omega) only [spec1, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e2 : spec2 n = n / 256 ^^^ n % 256 := by simp (disch := omega) only [spec2, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e3 : spec3 n = 0 := by simp (disch := omega) only [spec3, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e4 : spec4 n = 0 := by simp (disch := omega) only [spec4, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e5 : spec5 n = 0 := by simp (disch := omega) only [spec5, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e6 : spec6 n = 0 := by simp (disch := omega) only [spec6, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e7 : spec7 n = 0 := by simp (disch := omega) only [spec7, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have b0 : n / 256 < 256 := by omega
  have b1 : n % 256 < 256 := Nat.mod_lt _ (by decide)
  have b2 : n / 256 ^^^ n % 256 < 256 := Nat.xor_lt_two_pow (n := 8) b0 b1
  simp only [Vector.getElem_map, get0, get1, get2, get3, get4, get5, get6, get7, e0, e1, e2, e3,
    e4, e5, e6, e7, Nat.cast_zero]
  rw [val_cast (by omega), val_cast (by omega), val_cast (by omega)]
  exact ⟨b0, b1, b2, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Tag 58: XOR of two bytes, split into the two fragments of a rotation by `s`. -/
theorem split_facts {row : Vector (ZMod babyBearModulus) 9} (h : IsFormulaRow row)
    (tag : row[8] = 58) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 8 ∧
      row[3].val < 256 ∧ row[4].val < 256 ∧
      row[3].val = (row[0].val ^^^ row[1].val) * 2 ^ row[2].val % 256 ∧
      row[4].val = (row[0].val ^^^ row[1].val) / 2 ^ (8 - row[2].val) ∧
      row[5] = 0 ∧ row[6] = 0 ∧ row[7] = 0 := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 58) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : 65536 ≤ n ∧ n < 589824 := by unfold spec8 at t; split_ifs at t <;> omega
  have e0 : spec0 n = splitA n := by simp (disch := omega) only [spec0, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e1 : spec1 n = splitB n := by simp (disch := omega) only [spec1, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e2 : spec2 n = splitS n := by simp (disch := omega) only [spec2, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e3 : spec3 n = (splitA n ^^^ splitB n) * 2 ^ splitS n % 256 := by simp (disch := omega) only [spec3, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e4 : spec4 n = (splitA n ^^^ splitB n) / 2 ^ (8 - splitS n) := by simp (disch := omega) only [spec4, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e5 : spec5 n = 0 := by simp (disch := omega) only [spec5, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e6 : spec6 n = 0 := by simp (disch := omega) only [spec6, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e7 : spec7 n = 0 := by simp (disch := omega) only [spec7, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have b0 : splitA n < 256 := Nat.mod_lt _ (by decide)
  have b1 : splitB n < 256 := Nat.mod_lt _ (by decide)
  have b2 : splitS n < 8 := by simp only [splitS]; omega
  have bx : splitA n ^^^ splitB n < 256 := Nat.xor_lt_two_pow (n := 8) b0 b1
  have b3 : (splitA n ^^^ splitB n) * 2 ^ splitS n % 256 < 256 := Nat.mod_lt _ (by decide)
  have b4 : (splitA n ^^^ splitB n) / 2 ^ (8 - splitS n) < 256 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) bx
  simp only [Vector.getElem_map, get0, get1, get2, get3, get4, get5, get6, get7, e0, e1, e2, e3,
    e4, e5, e6, e7, Nat.cast_zero]
  rw [val_cast (by omega), val_cast (by omega), val_cast (by omega), val_cast (by omega),
    val_cast (by omega)]
  exact ⟨b0, b1, b2, b3, b4, by simp, by simp, by simp, by simp, by simp⟩

private theorem control_region {n : Nat}
    (tag : ((formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus)))[8] = 59) :
    589824 ≤ n ∧ n < 589945 := by
  have t := tag_of (t := 59) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  unfold spec8 at t; split_ifs at t <;> omega

/-- Tag 59: the execute column is boolean. -/
theorem control_execute {row : Vector (ZMod babyBearModulus) 9} (h : IsFormulaRow row)
    (tag : row[8] = 59) : row[1] = 0 ∨ row[1] = 1 := by
  obtain ⟨n, -, rfl⟩ := h
  have r := control_region tag
  rw [Vector.getElem_map, get1]
  by_cases z : n = 589824
  · left
    have : spec1 n = 0 := by simp (disch := omega) only [spec1, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
    rw [this, Nat.cast_zero]
  · right
    have : spec1 n = 1 := by simp (disch := omega) only [spec1, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
    rw [this, Nat.cast_one]

private theorem flag_cast (f i : Nat) :
    ((flag f i : Nat) : ZMod babyBearModulus) = if f = i % 5 then 1 else 0 := by
  unfold flag
  by_cases h : i % 5 = f
  · rw [ite_eq_left h, ite_eq_left h.symm, Nat.cast_one]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), Nat.cast_zero]

/-- Tag 59, executed: the controller row of a theta/rho call. -/
theorem control_facts {row : Vector (ZMod babyBearModulus) 9} (h : IsFormulaRow row)
    (tag : row[8] = 59) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .thetaRho ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      row[3] = (if 0 = index.val % 5 then 1 else 0) ∧
      row[4] = (if 1 = index.val % 5 then 1 else 0) ∧
      row[5] = (if 2 = index.val % 5 then 1 else 0) ∧
      row[6] = (if 3 = index.val % 5 then 1 else 0) ∧
      row[7] = (if 4 = index.val % 5 then 1 else 0) := by
  obtain ⟨n, -, rfl⟩ := h
  have r := control_region tag
  have nz : n ≠ 589824 := by
    rintro rfl
    rw [Vector.getElem_map, get1] at active
    have : spec1 589824 = 0 := by simp (disch := omega) only [spec1, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
    rw [this, Nat.cast_zero] at active
    exact zero_ne_one active
  have j : callAt (n - 589824) < 361 := callIndex_lt (by omega) (by omega) (by omega)
  have e0 : spec0 n = controlAt (callAt (n - 589824)) := by simp (disch := omega) only [spec0, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e2 : spec2 n = bump (controlAt (callAt (n - 589824))) := by simp (disch := omega) only [spec2, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e3 : spec3 n = flag 0 (callAt (n - 589824)) := by simp (disch := omega) only [spec3, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e4 : spec4 n = flag 1 (callAt (n - 589824)) := by simp (disch := omega) only [spec4, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e5 : spec5 n = flag 2 (callAt (n - 589824)) := by simp (disch := omega) only [spec5, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e6 : spec6 n = flag 3 (callAt (n - 589824)) := by simp (disch := omega) only [spec6, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e7 : spec7 n = flag 4 (callAt (n - 589824)) := by simp (disch := omega) only [spec7, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  refine ⟨⟨callAt (n - 589824), j⟩, thetaRho_kindAt _, ?_, ?_, ?_⟩
  · rw [Vector.getElem_map, get0, e0]
  · rw [Vector.getElem_map, get2, e2]
  · simp only [Vector.getElem_map, get3, get4, get5, get6, get7, e3, e4, e5, e6, e7, flag_cast]
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩

/-- Tag 60 with the key of call `index`: the seven slots of that call. -/
theorem slot_facts {row : Vector (ZMod babyBearModulus) 9} (h : IsFormulaRow row)
    (tag : row[8] = 60) (index : Fin 361)
    (key : row[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus)) :
    row[1] = ((Call.slots index)[0].val : ZMod babyBearModulus) ∧
      row[2] = ((Call.slots index)[1].val : ZMod babyBearModulus) ∧
      row[3] = ((Call.slots index)[2].val : ZMod babyBearModulus) ∧
      row[4] = ((Call.slots index)[3].val : ZMod babyBearModulus) ∧
      row[5] = ((Call.slots index)[4].val : ZMod babyBearModulus) ∧
      row[6] = ((Call.slots index)[5].val : ZMod babyBearModulus) ∧
      row[7] = ((Call.slots index)[6].val : ZMod babyBearModulus) := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 60) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : 589945 ≤ n ∧ n < 590066 := by unfold spec8 at t; split_ifs at t <;> omega
  have ci := controlAt_lt index.isLt
  rw [Vector.getElem_map, get0] at key
  by_cases z : n = 589945
  · exfalso
    have : spec0 n = 0 := by simp (disch := omega) only [spec0, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
    rw [this] at key
    have := cast_inj (by omega) (by omega) key
    omega
  have j : callAt (n - 589945) < 361 := callIndex_lt (by omega) (by omega) (by omega)
  have e0 : spec0 n = controlAt (callAt (n - 589945)) + 2048 := by simp (disch := omega) only [spec0, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  rw [e0] at key
  have same : callAt (n - 589945) = index.val :=
    controlAt_inj j index.isLt (by have := controlAt_lt j; have := cast_inj (by omega) (by omega) key; omega)
  have hidx : (⟨_, j⟩ : Fin 361) = index := Fin.ext same
  have slot (lane : Nat) (hl : lane < 7) :
      slotNat (callAt (n - 589945)) lane = ((Call.slots index)[lane]).val := by
    rw [slotNat_eq j hl, hidx]
  have e1 : spec1 n = slotNat (callAt (n - 589945)) 0 := by simp (disch := omega) only [spec1, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e2 : spec2 n = slotNat (callAt (n - 589945)) 1 := by simp (disch := omega) only [spec2, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e3 : spec3 n = slotNat (callAt (n - 589945)) 2 := by simp (disch := omega) only [spec3, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e4 : spec4 n = slotNat (callAt (n - 589945)) 3 := by simp (disch := omega) only [spec4, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e5 : spec5 n = slotNat (callAt (n - 589945)) 4 := by simp (disch := omega) only [spec5, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e6 : spec6 n = slotNat (callAt (n - 589945)) 5 := by simp (disch := omega) only [spec6, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  have e7 : spec7 n = slotNat (callAt (n - 589945)) 6 := by simp (disch := omega) only [spec7, ctl, slt, ite_eq_left, ite_eq_right, ite_true, ite_false]
  simp only [Vector.getElem_map, get1, get2, get3, get4, get5, get6, get7, e1, e2, e3, e4, e5,
    e6, e7, slot 0 (by omega), slot 1 (by omega), slot 2 (by omega), slot 3 (by omega),
    slot 4 (by omega), slot 5 (by omega), slot 6 (by omega)]
  exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

end Airbender.Keccak.Split.ThetaRho.SetupProofs
