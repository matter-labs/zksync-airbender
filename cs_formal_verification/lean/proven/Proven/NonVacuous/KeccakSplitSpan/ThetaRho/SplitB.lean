module
public import Proven.NonVacuous.KeccakSplitSpan.ThetaRho.SplitA

@[expose] public section

/-! The XOR-and-split queries of theta+rho lanes 2 (bytes 4 to 7) to 4 hold for the honest assignment of
    valid inputs, over BabyBear (`SplitA.lean`). -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

variable {p : Nat} [Fact p.Prime]

theorem lookup_31 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨31, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 2 4) (b := d x 4) (s := shift x 2) (inByte_lt valid kind (by decide) 4)
      (d_lt valid kind 4)
    (shift_lt x 2) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_32 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨32, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 2 5) (b := d x 5) (s := shift x 2) (inByte_lt valid kind (by decide) 5)
      (d_lt valid kind 5)
    (shift_lt x 2) (by quotient (-7864320) (show x.limb 2 2 = x.limb 2 2 % 256 + 256 * inByte x 2 5 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_33 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨33, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 2 6) (b := d x 6) (s := shift x 2) (inByte_lt valid kind (by decide) 6)
      (d_lt valid kind 6)
    (shift_lt x 2) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_34 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨34, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 2) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 2 7) (b := d x 7) (s := shift x 2) (inByte_lt valid kind (by decide) 7)
      (d_lt valid kind 7)
    (shift_lt x 2) (by quotient (-7864320) (show x.limb 2 3 = x.limb 2 3 % 256 + 256 * inByte x 2 7 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_2 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_35 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨35, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 3 0) (b := d x 0) (s := shift x 3) (inByte_lt valid kind (by decide) 0)
      (d_lt valid kind 0)
    (shift_lt x 3) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_36 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨36, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 3 1) (b := d x 1) (s := shift x 3) (inByte_lt valid kind (by decide) 1)
      (d_lt valid kind 1)
    (shift_lt x 3) (by quotient (-7864320) (show x.limb 3 0 = x.limb 3 0 % 256 + 256 * inByte x 3 1 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_37 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨37, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 3 2) (b := d x 2) (s := shift x 3) (inByte_lt valid kind (by decide) 2)
      (d_lt valid kind 2)
    (shift_lt x 3) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_38 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨38, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 3 3) (b := d x 3) (s := shift x 3) (inByte_lt valid kind (by decide) 3)
      (d_lt valid kind 3)
    (shift_lt x 3) (by quotient (-7864320) (show x.limb 3 1 = x.limb 3 1 % 256 + 256 * inByte x 3 3 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_39 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨39, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 3 4) (b := d x 4) (s := shift x 3) (inByte_lt valid kind (by decide) 4)
      (d_lt valid kind 4)
    (shift_lt x 3) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_40 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨40, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 3 5) (b := d x 5) (s := shift x 3) (inByte_lt valid kind (by decide) 5)
      (d_lt valid kind 5)
    (shift_lt x 3) (by quotient (-7864320) (show x.limb 3 2 = x.limb 3 2 % 256 + 256 * inByte x 3 5 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_41 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨41, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 3 6) (b := d x 6) (s := shift x 3) (inByte_lt valid kind (by decide) 6)
      (d_lt valid kind 6)
    (shift_lt x 3) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_42 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨42, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 3) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 3 7) (b := d x 7) (s := shift x 3) (inByte_lt valid kind (by decide) 7)
      (d_lt valid kind 7)
    (shift_lt x 3) (by quotient (-7864320) (show x.limb 3 3 = x.limb 3 3 % 256 + 256 * inByte x 3 7 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_3 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_43 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨43, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 4 0) (b := d x 0) (s := shift x 4) (inByte_lt valid kind (by decide) 0)
      (d_lt valid kind 0)
    (shift_lt x 4) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_44 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨44, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 0
  op_index
  exact split_at (a := inByte x 4 1) (b := d x 1) (s := shift x 4) (inByte_lt valid kind (by decide) 1)
      (d_lt valid kind 1)
    (shift_lt x 4) (by quotient (-7864320) (show x.limb 4 0 = x.limb 4 0 % 256 + 256 * inByte x 4 1 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_45 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨45, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 4 2) (b := d x 2) (s := shift x 4) (inByte_lt valid kind (by decide) 2)
      (d_lt valid kind 2)
    (shift_lt x 4) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_46 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨46, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 1
  op_index
  exact split_at (a := inByte x 4 3) (b := d x 3) (s := shift x 4) (inByte_lt valid kind (by decide) 3)
      (d_lt valid kind 3)
    (shift_lt x 4) (by quotient (-7864320) (show x.limb 4 1 = x.limb 4 1 % 256 + 256 * inByte x 4 3 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_47 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨47, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 4 4) (b := d x 4) (s := shift x 4) (inByte_lt valid kind (by decide) 4)
      (d_lt valid kind 4)
    (shift_lt x 4) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_48 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨48, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 2
  op_index
  exact split_at (a := inByte x 4 5) (b := d x 5) (s := shift x 4) (inByte_lt valid kind (by decide) 5)
      (d_lt valid kind 5)
    (shift_lt x 4) (by quotient (-7864320) (show x.limb 4 2 = x.limb 4 2 % 256 + 256 * inByte x 4 5 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_49 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨49, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 4 6) (b := d x 6) (s := shift x 4) (inByte_lt valid kind (by decide) 6)
      (d_lt valid kind 6)
    (shift_lt x 4) (by theta_direct)
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

theorem lookup_50 (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨50, by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraints
        (ThetaRho.setup (p := p)))).length = 51 := by rfl
      omega⟩).Contains (Verification.environment (assignment x)) := by
  subst hp
  have := valid.limb (l := 4) (by rw [kind]; decide) 3
  op_index
  exact split_at (a := inByte x 4 7) (b := d x 7) (s := shift x 4) (inByte_lt valid kind (by decide) 7)
      (d_lt valid kind 7)
    (shift_lt x 4) (by quotient (-7864320) (show x.limb 4 3 = x.limb 4 3 % 256 + 256 * inByte x 4 7 by
      simp only [inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
    (by theta_direct) (by cast_identity 2013265921 (shift_4 x)) (by theta_result) (by theta_result)
    (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
