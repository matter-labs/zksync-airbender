module
public import Proven.KeccakSplit.Setup.ColumnParity.Spec
public import Proven.KeccakSplit.Setup.Facts

@[expose] public section

/- Meaning of the column-parity formula rows, by tag, over BabyBear. -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- The row formulas, one per column. -/
def formulaRow (n : Nat) : Vector Nat 8 :=
  #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n, spec6 n, spec7 n]

theorem get0 (n : Nat) : (formulaRow n)[0] = spec0 n := by rfl
theorem get1 (n : Nat) : (formulaRow n)[1] = spec1 n := by rfl
theorem get2 (n : Nat) : (formulaRow n)[2] = spec2 n := by rfl
theorem get3 (n : Nat) : (formulaRow n)[3] = spec3 n := by rfl
theorem get4 (n : Nat) : (formulaRow n)[4] = spec4 n := by rfl
theorem get5 (n : Nat) : (formulaRow n)[5] = spec5 n := by rfl
theorem get6 (n : Nat) : (formulaRow n)[6] = spec6 n := by rfl
theorem get7 (n : Nat) : (formulaRow n)[7] = spec7 n := by rfl

/-- A field row that is the cast of a formula row of the trace. -/
def IsFormulaRow (row : Vector (ZMod babyBearModulus) 8) : Prop :=
  ∃ n < 4194304, row = (formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus))

private theorem tag_of {n t : Nat} (ht : t ≤ 64)
    (h : ((formulaRow n).map (fun v : Nat => (v : ZMod babyBearModulus)))[7] =
      (t : ZMod babyBearModulus)) : spec7 n = t := by
  have le : spec7 n ≤ 64 := by unfold spec7; split_ifs <;> omega
  rw [Vector.getElem_map, get7] at h
  exact cast_inj (by omega) (by omega) h

/-- Tag 64: the XOR of five nibbles. -/
theorem xor5_facts {row : Vector (ZMod babyBearModulus) 8} (h : IsFormulaRow row)
    (tag : row[7] = 64) :
    (row[0].val < 16 ∧ row[1].val < 16 ∧ row[2].val < 16 ∧ row[3].val < 16 ∧ row[4].val < 16) ∧
      row[5].val < 16 ∧
      row[5].val = row[0].val ^^^ row[1].val ^^^ row[2].val ^^^ row[3].val ^^^ row[4].val ∧
      row[6] = 0 := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 64) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : 65780 ≤ n ∧ n < 1114356 := by unfold spec7 at t; split_ifs at t <;> omega
  have e0 : spec0 n = nib (n - 65780) 0 := by unfold spec0; region
  have e1 : spec1 n = nib (n - 65780) 1 := by unfold spec1; region
  have e2 : spec2 n = nib (n - 65780) 2 := by unfold spec2; region
  have e3 : spec3 n = nib (n - 65780) 3 := by unfold spec3; region
  have e4 : spec4 n = nib (n - 65780) 4 := by unfold spec4; region
  have e5 : spec5 n = nib (n - 65780) 0 ^^^ nib (n - 65780) 1 ^^^ nib (n - 65780) 2 ^^^
      nib (n - 65780) 3 ^^^ nib (n - 65780) 4 := by unfold spec5; region
  have e6 : spec6 n = 0 := by unfold spec6; region
  have x5 : nib (n - 65780) 0 ^^^ nib (n - 65780) 1 ^^^ nib (n - 65780) 2 ^^^
      nib (n - 65780) 3 ^^^ nib (n - 65780) 4 < 16 :=
    Nat.xor_lt_two_pow (n := 4) (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (nib_lt _ _) (nib_lt _ _)) (nib_lt _ _)) (nib_lt _ _)) (nib_lt _ _)
  have v (k : Nat) : ((nib (n - 65780) k : Nat) : ZMod babyBearModulus).val = nib (n - 65780) k :=
    val_cast (by have := nib_lt (n - 65780) k; omega)
  simp only [Vector.getElem_map, get0, get1, get2, get3, get4, get5, get6, e0, e1, e2, e3, e4,
    e5, e6, v, Nat.cast_zero]
  rw [val_cast (by omega)]
  exact ⟨⟨nib_lt _ _, nib_lt _ _, nib_lt _ _, nib_lt _ _, nib_lt _ _⟩, x5, by simp, by simp⟩

/-- Tag 38: the iota byte XOR `a ^ iotaByte b`. -/
theorem iota_facts {row : Vector (ZMod babyBearModulus) 8} (h : IsFormulaRow row)
    (tag : row[7] = 38) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ Airbender.Keccak.iotaByte row[1].val ∧
      row[3] = 0 ∧ row[4] = 0 ∧ row[5] = 0 ∧ row[6] = 0 := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 38) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : n < 65536 := by unfold spec7 at t; split_ifs at t <;> omega
  have e0 : spec0 n = n % 256 := by unfold spec0; region
  have e1 : spec1 n = n / 256 := by unfold spec1; region
  have e2 : spec2 n = n % 256 ^^^ rcByte (n / 256) := by unfold spec2; region
  have e3 : spec3 n = 0 := by unfold spec3; region
  have e4 : spec4 n = 0 := by unfold spec4; region
  have e5 : spec5 n = 0 := by unfold spec5; region
  have e6 : spec6 n = 0 := by unfold spec6; region
  have b0 : n % 256 < 256 := Nat.mod_lt _ (by decide)
  have b1 : n / 256 < 256 := by omega
  have rc : rcByte (n / 256) < 256 := Nat.mod_lt _ (by decide)
  have b2 : n % 256 ^^^ rcByte (n / 256) < 256 := Nat.xor_lt_two_pow (n := 8) b0 rc
  simp only [Vector.getElem_map, get0, get1, get2, get3, get4, get5, get6, e0, e1, e2, e3, e4,
    e5, e6, Nat.cast_zero]
  rw [val_cast (by omega), val_cast (by omega), val_cast (by omega),
    ← rcByte_eq_iotaByte _ b1]
  exact ⟨b0, b1, b2, by simp, by simp, by simp, by simp, by simp⟩

/-- Tag 63, executed: the controller row of a column-parity call. -/
theorem control_facts {row : Vector (ZMod babyBearModulus) 8} (h : IsFormulaRow row)
    (tag : row[7] = 63) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .columnParity ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      row[3] = ((if index.val % 5 = 0 then index.val / 15 else 0 : Nat) : ZMod babyBearModulus) := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 63) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : 65658 ≤ n ∧ n < 65780 := by unfold spec7 at t; split_ifs at t <;> omega
  have nz : n ≠ 65658 := by
    rintro rfl
    rw [Vector.getElem_map, get1] at active
    have : spec1 65658 = 0 := by unfold spec1; region
    rw [this, Nat.cast_zero] at active
    exact zero_ne_one active
  have e0 : spec0 n = controlAt (callAt (n - 65658)) := by unfold spec0; region
  have e2 : spec2 n = bump (controlAt (callAt (n - 65658))) := by unfold spec2; region
  have e3 : spec3 n = if callAt (n - 65658) % 5 = 0 then callAt (n - 65658) / 15 else 0 := by
    unfold spec3; region
  refine ⟨⟨callAt (n - 65658), parity_callIndex_lt (by omega) (by omega)⟩,
    parity_kindAt _, ?_, ?_, ?_⟩
  · rw [Vector.getElem_map, get0, e0]
  · rw [Vector.getElem_map, get2, e2]
  · rw [Vector.getElem_map, get3, e3]

/-- Tag 62 with the key of call `index`: the six slots of that call. -/
theorem slot_facts {row : Vector (ZMod babyBearModulus) 8} (h : IsFormulaRow row)
    (tag : row[7] = 62) (index : Fin 361)
    (key : row[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus)) :
    row[1] = ((Call.slots index)[0].val : ZMod babyBearModulus) ∧
      row[2] = ((Call.slots index)[1].val : ZMod babyBearModulus) ∧
      row[3] = ((Call.slots index)[2].val : ZMod babyBearModulus) ∧
      row[4] = ((Call.slots index)[3].val : ZMod babyBearModulus) ∧
      row[5] = ((Call.slots index)[4].val : ZMod babyBearModulus) ∧
      row[6] = ((Call.slots index)[5].val : ZMod babyBearModulus) := by
  obtain ⟨n, -, rfl⟩ := h
  have t := tag_of (t := 62) (by omega) (tag.trans (Nat.cast_ofNat).symm)
  have r : 65536 ≤ n ∧ n < 65658 := by unfold spec7 at t; split_ifs at t <;> omega
  have ci := controlAt_lt index.isLt
  rw [Vector.getElem_map, get0] at key
  by_cases z : n = 65536
  · exfalso
    have : spec0 n = 0 := by unfold spec0; region
    rw [this] at key
    have := cast_inj (by omega) (by omega) key
    omega
  have j : callAt (n - 65536) < 361 := parity_callIndex_lt (by omega) (by omega)
  have e0 : spec0 n = controlAt (callAt (n - 65536)) + 2048 := by unfold spec0; region
  rw [e0] at key
  have same : callAt (n - 65536) = index.val :=
    controlAt_inj j index.isLt (by have := controlAt_lt j; have := cast_inj (by omega) (by omega) key; omega)
  have hidx : (⟨_, j⟩ : Fin 361) = index := Fin.ext same
  have slot (lane : Nat) (hl : lane < 7) :
      slotNat (callAt (n - 65536)) lane = ((Call.slots index)[lane]).val := by
    rw [slotNat_eq j hl, hidx]
  have e1 : spec1 n = slotNat (callAt (n - 65536)) 0 := by unfold spec1; region
  have e2 : spec2 n = slotNat (callAt (n - 65536)) 1 := by unfold spec2; region
  have e3 : spec3 n = slotNat (callAt (n - 65536)) 2 := by unfold spec3; region
  have e4 : spec4 n = slotNat (callAt (n - 65536)) 3 := by unfold spec4; region
  have e5 : spec5 n = slotNat (callAt (n - 65536)) 4 := by unfold spec5; region
  have e6 : spec6 n = slotNat (callAt (n - 65536)) 5 := by unfold spec6; region
  simp only [Vector.getElem_map, get1, get2, get3, get4, get5, get6, e1, e2, e3, e4, e5, e6,
    slot 0 (by omega), slot 1 (by omega), slot 2 (by omega), slot 3 (by omega), slot 4 (by omega),
    slot 5 (by omega)]
  exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩

end Airbender.Keccak.Split.ColumnParity.SetupProofs
