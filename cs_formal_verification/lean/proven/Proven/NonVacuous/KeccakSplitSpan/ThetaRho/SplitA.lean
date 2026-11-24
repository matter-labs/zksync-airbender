module
public import Proven.NonVacuous.KeccakSplitSpan.ThetaRho.Values

@[expose] public section

/-! The XOR-and-split queries of theta+rho lanes 0 to 2 (bytes 0 to 3 of lane 2) hold for the honest
    assignment of valid inputs, over BabyBear: each lane byte, the `D` byte and the lane's shift select the setup
    row whose fragments are the honest ones. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

variable {p : Nat} [Fact p.Prime]

theorem lookup_11 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨11, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 0 0) (b := d x 0) (s := shift x 0) (inByte_lt valid kind (by decide) 0)
      (d_lt valid kind 0)
    (shift_lt x 0) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_12 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨12, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 0 1) (b := d x 1) (s := shift x 0) (inByte_lt valid kind (by decide) 1)
      (d_lt valid kind 1)
    (shift_lt x 0) (by quotient (-7864320) (show x.limb 0 0 = x.limb 0 0 % 256 + 256 * inByte x 0 1 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_13 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨13, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 0 2) (b := d x 2) (s := shift x 0) (inByte_lt valid kind (by decide) 2)
      (d_lt valid kind 2)
    (shift_lt x 0) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_14 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨14, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 0 3) (b := d x 3) (s := shift x 0) (inByte_lt valid kind (by decide) 3)
      (d_lt valid kind 3)
    (shift_lt x 0) (by quotient (-7864320) (show x.limb 0 1 = x.limb 0 1 % 256 + 256 * inByte x 0 3 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_15 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨15, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 0 4) (b := d x 4) (s := shift x 0) (inByte_lt valid kind (by decide) 4)
      (d_lt valid kind 4)
    (shift_lt x 0) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_16 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨16, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 0 5) (b := d x 5) (s := shift x 0) (inByte_lt valid kind (by decide) 5)
      (d_lt valid kind 5)
    (shift_lt x 0) (by quotient (-7864320) (show x.limb 0 2 = x.limb 0 2 % 256 + 256 * inByte x 0 5 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_17 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨17, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 0 6) (b := d x 6) (s := shift x 0) (inByte_lt valid kind (by decide) 6)
      (d_lt valid kind 6)
    (shift_lt x 0) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_18 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨18, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 0) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 0 7) (b := d x 7) (s := shift x 0) (inByte_lt valid kind (by decide) 7)
      (d_lt valid kind 7)
    (shift_lt x 0) (by quotient (-7864320) (show x.limb 0 3 = x.limb 0 3 % 256 + 256 * inByte x 0 7 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_0 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_19 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨19, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 1 0) (b := d x 0) (s := shift x 1) (inByte_lt valid kind (by decide) 0)
      (d_lt valid kind 0)
    (shift_lt x 1) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_20 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨20, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 1 1) (b := d x 1) (s := shift x 1) (inByte_lt valid kind (by decide) 1)
      (d_lt valid kind 1)
    (shift_lt x 1) (by quotient (-7864320) (show x.limb 1 0 = x.limb 1 0 % 256 + 256 * inByte x 1 1 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_21 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨21, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 1 2) (b := d x 2) (s := shift x 1) (inByte_lt valid kind (by decide) 2)
      (d_lt valid kind 2)
    (shift_lt x 1) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_22 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨22, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 1 3) (b := d x 3) (s := shift x 1) (inByte_lt valid kind (by decide) 3)
      (d_lt valid kind 3)
    (shift_lt x 1) (by quotient (-7864320) (show x.limb 1 1 = x.limb 1 1 % 256 + 256 * inByte x 1 3 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_23 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨23, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 1 4) (b := d x 4) (s := shift x 1) (inByte_lt valid kind (by decide) 4)
      (d_lt valid kind 4)
    (shift_lt x 1) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_24 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨24, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 1 5) (b := d x 5) (s := shift x 1) (inByte_lt valid kind (by decide) 5)
      (d_lt valid kind 5)
    (shift_lt x 1) (by quotient (-7864320) (show x.limb 1 2 = x.limb 1 2 % 256 + 256 * inByte x 1 5 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_25 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨25, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 1 6) (b := d x 6) (s := shift x 1) (inByte_lt valid kind (by decide) 6)
      (d_lt valid kind 6)
    (shift_lt x 1) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_26 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨26, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 1) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 1 7) (b := d x 7) (s := shift x 1) (inByte_lt valid kind (by decide) 7)
      (d_lt valid kind 7)
    (shift_lt x 1) (by quotient (-7864320) (show x.limb 1 3 = x.limb 1 3 % 256 + 256 * inByte x 1 7 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_1 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_27 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨27, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 2 0) (b := d x 0) (s := shift x 2) (inByte_lt valid kind (by decide) 0)
      (d_lt valid kind 0)
    (shift_lt x 2) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_28 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨28, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 2 1) (b := d x 1) (s := shift x 2) (inByte_lt valid kind (by decide) 1)
      (d_lt valid kind 1)
    (shift_lt x 2) (by quotient (-7864320) (show x.limb 2 0 = x.limb 2 0 % 256 + 256 * inByte x 2 1 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_29 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨29, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 2 2) (b := d x 2) (s := shift x 2) (inByte_lt valid kind (by decide) 2)
      (d_lt valid kind 2)
    (shift_lt x 2) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_30 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨30, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 2 3) (b := d x 3) (s := shift x 2) (inByte_lt valid kind (by decide) 3)
      (d_lt valid kind 3)
    (shift_lt x 2) (by quotient (-7864320) (show x.limb 2 1 = x.limb 2 1 % 256 + 256 * inByte x 2 3 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
