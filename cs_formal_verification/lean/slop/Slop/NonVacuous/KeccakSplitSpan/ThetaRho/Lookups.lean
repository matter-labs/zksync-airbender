module
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.SplitB

@[expose] public section

/-! The 51 imported lookups of a theta+rho row hold for the honest assignment of valid inputs, over BabyBear: the
    pointer alignment, the slot query, the eight byte XOR queries of `D`, the control query, and the forty
    XOR-and-split queries (`SplitA.lean`, `SplitB.lean`). -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

variable {p : Nat} [Fact p.Prime]

theorem lookups (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).length),
      ((FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get ⟨i, h⟩).Contains
        (Verification.environment (assignment x)) := by
  subst hp
  have pointer := valid.pointer
  simp only [Word.Bounded, limbBase] at pointer
  have c0 := valid.limb (l := 5) (by rw [kind]; decide) 0
  have c1 := valid.limb (l := 5) (by rw [kind]; decide) 1
  have c2 := valid.limb (l := 5) (by rw [kind]; decide) 2
  have c3 := valid.limb (l := 5) (by rw [kind]; decide) 3
  have n0 := valid.limb (l := 6) (by rw [kind]; decide) 0
  have n1 := valid.limb (l := 6) (by rw [kind]; decide) 1
  have n2 := valid.limb (l := 6) (by rw [kind]; decide) 2
  have n3 := valid.limb (l := 6) (by rw [kind]; decide) 3
  intro i h
  have size : i < 51 := by
    have count : (FlatOperation.lookups (ThetaRho.importedConstraints
      (ThetaRho.setup (p := 2013265921)))).length = 51 := by rfl
    omega
  interval_cases i
  · op_index
    refine range_of_eval (n := (x.read 1).lo / 256) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient (-7864320) (show (x.read 1).lo = 256 * ((x.read 1).lo / 256) by omega)
  · op_index
    exact slots_at valid.call kind (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
      (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 0) (b := rByte x 0) (cByte_lt valid kind 0) (rByte_lt valid kind 0)
        (by theta_direct)
        (by theta_direct)
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 1) (b := rByte x 1) (cByte_lt valid kind 1) (rByte_lt valid kind 1)
        (by quotient (-7864320) (show x.limb 5 0 = x.limb 5 0 % 256 + 256 * cByte x 1 by
          simp only [cByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
        (by quotient (-7864320) (show 2 * x.limb 6 0 + top x 3 = 65536 * top x 0 + rotLimb x 0 % 256 +
          256 * rByte x 1 by
          simp only [rByte, rotLimb, top, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]
          omega))
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 2) (b := rByte x 2) (cByte_lt valid kind 2) (rByte_lt valid kind 2)
        (by theta_direct)
        (by theta_direct)
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 3) (b := rByte x 3) (cByte_lt valid kind 3) (rByte_lt valid kind 3)
        (by quotient (-7864320) (show x.limb 5 1 = x.limb 5 1 % 256 + 256 * cByte x 3 by
          simp only [cByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
        (by quotient (-7864320) (show 2 * x.limb 6 1 + top x 0 = 65536 * top x 1 + rotLimb x 1 % 256 +
          256 * rByte x 3 by
          simp only [rByte, rotLimb, top, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]
          omega))
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 4) (b := rByte x 4) (cByte_lt valid kind 4) (rByte_lt valid kind 4)
        (by theta_direct)
        (by theta_direct)
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 5) (b := rByte x 5) (cByte_lt valid kind 5) (rByte_lt valid kind 5)
        (by quotient (-7864320) (show x.limb 5 2 = x.limb 5 2 % 256 + 256 * cByte x 5 by
          simp only [cByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
        (by quotient (-7864320) (show 2 * x.limb 6 2 + top x 1 = 65536 * top x 2 + rotLimb x 2 % 256 +
          256 * rByte x 5 by
          simp only [rByte, rotLimb, top, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]
          omega))
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 6) (b := rByte x 6) (cByte_lt valid kind 6) (rByte_lt valid kind 6)
        (by theta_direct)
        (by theta_direct)
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact byte_xor_at (a := cByte x 7) (b := rByte x 7) (cByte_lt valid kind 7) (rByte_lt valid kind 7)
        (by quotient (-7864320) (show x.limb 5 3 = x.limb 5 3 % 256 + 256 * cByte x 7 by
          simp only [cByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]; omega))
        (by quotient (-7864320) (show 2 * x.limb 6 3 + top x 2 = 65536 * top x 3 + rotLimb x 3 % 256 +
          256 * rByte x 7 by
          simp only [rByte, rotLimb, top, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]
          omega))
        (by theta_result) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
        (by theta_direct)
  · op_index
    exact control_at valid.call kind (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
      (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct) (by theta_direct)
  · exact lookup_11 x valid kind rfl
  · exact lookup_12 x valid kind rfl
  · exact lookup_13 x valid kind rfl
  · exact lookup_14 x valid kind rfl
  · exact lookup_15 x valid kind rfl
  · exact lookup_16 x valid kind rfl
  · exact lookup_17 x valid kind rfl
  · exact lookup_18 x valid kind rfl
  · exact lookup_19 x valid kind rfl
  · exact lookup_20 x valid kind rfl
  · exact lookup_21 x valid kind rfl
  · exact lookup_22 x valid kind rfl
  · exact lookup_23 x valid kind rfl
  · exact lookup_24 x valid kind rfl
  · exact lookup_25 x valid kind rfl
  · exact lookup_26 x valid kind rfl
  · exact lookup_27 x valid kind rfl
  · exact lookup_28 x valid kind rfl
  · exact lookup_29 x valid kind rfl
  · exact lookup_30 x valid kind rfl
  · exact lookup_31 x valid kind rfl
  · exact lookup_32 x valid kind rfl
  · exact lookup_33 x valid kind rfl
  · exact lookup_34 x valid kind rfl
  · exact lookup_35 x valid kind rfl
  · exact lookup_36 x valid kind rfl
  · exact lookup_37 x valid kind rfl
  · exact lookup_38 x valid kind rfl
  · exact lookup_39 x valid kind rfl
  · exact lookup_40 x valid kind rfl
  · exact lookup_41 x valid kind rfl
  · exact lookup_42 x valid kind rfl
  · exact lookup_43 x valid kind rfl
  · exact lookup_44 x valid kind rfl
  · exact lookup_45 x valid kind rfl
  · exact lookup_46 x valid kind rfl
  · exact lookup_47 x valid kind rfl
  · exact lookup_48 x valid kind rfl
  · exact lookup_49 x valid kind rfl
  · exact lookup_50 x valid kind rfl

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
