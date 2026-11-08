module
public import Human.Circuits.UnifiedReduced.Artifact
public import Human.Helpers.Core.BabyBearPrime
public import Slop.Constraints
public import Slop.Trace.Timestamps
public import Slop.UnifiedReduced.Completeness.Attr

@[expose] public section

/-! Completeness of the family-independent row frame of the unified circuit: the
    program counter and clock increments, and the eight timestamp range queries of
    the three memory ports. Stated once over symbolic values. -/

namespace Airbender.UnifiedReduced.Completeness
open Verification
set_option warningAsError true

/-- Timing inputs of one honest row: initial PC and clock limbs, and the previous
    access clock of each of the three memory ports. -/
structure Frame where
  pcLo : Nat
  pcHi : Nat
  tsLo : Nat
  tsHi : Nat
  prev0Lo : Nat
  prev0Hi : Nat
  prev1Lo : Nat
  prev1Hi : Nat
  prev2Lo : Nat
  prev2Hi : Nat

/-- Borrow of the low-limb comparison of a previous clock against `ts + k`. -/
def borrow (prevLo tsLo k : Nat) : Nat := if prevLo < tsLo + k then 1 else 0

namespace Frame

def pcCarry (f : Frame) : Nat := (f.pcLo + 4) / 65536
def finalPcLo (f : Frame) : Nat := (f.pcLo + 4) % 65536
def finalPcHi (f : Frame) : Nat := f.pcHi + f.pcCarry
def tsCarry (f : Frame) : Nat := (f.tsLo + 4) / 524288
def finalTsLo (f : Frame) : Nat := (f.tsLo + 4) % 524288
def finalTsHi (f : Frame) : Nat := f.tsHi + f.tsCarry
def borrow0 (f : Frame) : Nat := borrow f.prev0Lo f.tsLo 0
def borrow1 (f : Frame) : Nat := borrow f.prev1Lo f.tsLo 1
def borrow2 (f : Frame) : Nat := borrow f.prev2Lo f.tsLo 2

/-- Range conditions of an honest frame: limbs in range, no PC or clock overflow,
    and every previous port access strictly before its in-row clock. -/
structure Valid (f : Frame) : Prop where
  pcLo : f.pcLo < 65536
  pcHi : f.finalPcHi < 65536
  tsLo : f.tsLo + 2 < 524288
  tsHi : f.finalTsHi < 524288
  prev0Lo : f.prev0Lo < 524288
  prev1Lo : f.prev1Lo < 524288
  prev2Lo : f.prev2Lo < 524288
  prev0 : f.prev0Hi * 524288 + f.prev0Lo < f.tsHi * 524288 + f.tsLo
  prev1 : f.prev1Hi * 524288 + f.prev1Lo < f.tsHi * 524288 + f.tsLo + 1
  prev2 : f.prev2Hi * 524288 + f.prev2Lo < f.tsHi * 524288 + f.tsLo + 2

/-- The PC and clock bounds alone (no ordering of the previous port accesses). -/
structure Clock (f : Frame) : Prop where
  pcLo : f.pcLo < 65536
  pcHi : f.finalPcHi < 65536
  tsLo : f.tsLo + 2 < 524288

theorem Valid.clock {f : Frame} (h : f.Valid) : f.Clock := ⟨h.pcLo, h.pcHi, h.tsLo⟩

/-- The clock columns an assignment places for a frame. -/
structure Columns (f : Frame) (w : Nat → ZMod babyBearModulus) : Prop where
  tsLo : w 2 = f.tsLo
  tsHi : w 3 = f.tsHi
  finalTsLo : w 32 = f.finalTsLo
  finalTsHi : w 33 = f.finalTsHi
  prev0Lo : w 34 = f.prev0Lo
  prev0Hi : w 35 = f.prev0Hi
  prev1Lo : w 40 = f.prev1Lo
  prev1Hi : w 41 = f.prev1Hi
  prev2Lo : w 46 = f.prev2Lo
  prev2Hi : w 47 = f.prev2Hi
  borrow0 : w 123 = f.borrow0
  borrow1 : w 124 = f.borrow1
  borrow2 : w 125 = f.borrow2

end Frame

theorem natCast_val_lt {n bound : Nat} (x : ZMod babyBearModulus) (h : x = n) (hn : n < bound)
    (hb : bound ≤ babyBearModulus) : x.val < bound := by
  subst h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  exact hn

/-- Normal form of imported constants: `Int.ofNat`/`Int.negSucc` casts become numerals. -/
theorem cast_ofNat (n : Nat) : ((Int.ofNat n : Int) : ZMod babyBearModulus) = (n : ZMod babyBearModulus) := by
  simp
theorem cast_negSucc (n : Nat) :
    ((Int.negSucc n : Int) : ZMod babyBearModulus) = -((n + 1 : Nat) : ZMod babyBearModulus) := by
  simp [Int.cast_negSucc]

private theorem port_lo (tsLo prevLo k : Nat) (hts : tsLo + 2 < 524288) (hprev : prevLo < 524288)
    (hk : k ≤ 2) (x : ZMod babyBearModulus)
    (hx : x = -(tsLo : ZMod babyBearModulus) + prevLo + 524288 * (borrow prevLo tsLo k : Nat) - k) :
    x.val < 524288 := by
  unfold borrow at hx
  split at hx
  · refine natCast_val_lt x (n := prevLo + 524288 - tsLo - k) ?_ (by omega) (by decide)
    have e : (((prevLo + 524288 - tsLo - k) + tsLo + k : Nat) : ZMod babyBearModulus) =
        ((prevLo + 524288 : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hx
    rw [hx]; linear_combination -e
  · refine natCast_val_lt x (n := prevLo - tsLo - k) ?_ (by omega) (by decide)
    have e : (((prevLo - tsLo - k) + tsLo + k : Nat) : ZMod babyBearModulus) =
        ((prevLo : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hx
    rw [hx]; linear_combination -e

private theorem port_hi (tsLo tsHi prevLo prevHi k : Nat) (hts : tsHi < 524288)
    (hprev : prevHi * 524288 + prevLo < tsHi * 524288 + tsLo + k)
    (htsLo : tsLo + 2 < 524288) (hk : k ≤ 2) (x : ZMod babyBearModulus)
    (hx : x = -(tsHi : ZMod babyBearModulus) + prevHi - (borrow prevLo tsLo k : Nat) + 524288) :
    x.val < 524288 := by
  unfold borrow at hx
  split at hx
  · have : prevHi ≤ tsHi := by omega
    refine natCast_val_lt x (n := prevHi + 524287 - tsHi) ?_ (by omega) (by decide)
    have e : (((prevHi + 524287 - tsHi) + tsHi + 1 : Nat) : ZMod babyBearModulus) =
        ((prevHi + 524288 : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hx
    rw [hx]; linear_combination -e
  · have : prevHi < tsHi := by omega
    refine natCast_val_lt x (n := prevHi + 524288 - tsHi) ?_ (by omega) (by decide)
    have e : (((prevHi + 524288 - tsHi) + tsHi : Nat) : ZMod babyBearModulus) =
        ((prevHi + 524288 : Nat) : ZMod babyBearModulus) := congrArg _ (by omega)
    push_cast at e hx
    rw [hx]; linear_combination -e

/-- The eight native timestamp range queries hold for every valid frame. -/
theorem Frame.timestamps {f : Frame} (hf : f.Valid) {w : Nat → ZMod babyBearModulus}
    (hw : f.Columns w) : FlatOperation.ConstraintsHoldFlat (environment w)
      importedConstraintsTimestampLookups := by
  have hi : f.tsHi < 524288 := by have := hf.tsHi; unfold Frame.finalTsHi at this; omega
  simp only [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals apply Trace.Proofs.range_contains
  all_goals simp only [Trace.timestampBase, Expression.eval, environment, hw.tsLo, hw.tsHi,
    hw.finalTsLo, hw.finalTsHi, hw.prev0Lo, hw.prev0Hi, hw.prev1Lo, hw.prev1Hi, hw.prev2Lo,
    hw.prev2Hi, hw.borrow0, hw.borrow1, hw.borrow2, Frame.borrow0, Frame.borrow1, Frame.borrow2,
    cast_ofNat, cast_negSucc]
  · exact natCast_val_lt _ (n := f.finalTsLo) (by push_cast; ring)
      (by unfold Frame.finalTsLo; omega) (by decide)
  · exact natCast_val_lt _ (n := f.finalTsHi) (by push_cast; ring) hf.tsHi (by decide)
  · exact port_lo _ _ 0 hf.tsLo hf.prev0Lo (by decide) _ (by push_cast; ring)
  · exact port_hi _ _ _ _ 0 hi (by simpa using hf.prev0) hf.tsLo (by decide) _ (by push_cast; ring)
  · exact port_lo _ _ 1 hf.tsLo hf.prev1Lo (by decide) _ (by push_cast; ring)
  · exact port_hi _ _ _ _ 1 hi hf.prev1 hf.tsLo (by decide) _ (by push_cast; ring)
  · exact port_lo _ _ 2 hf.tsLo hf.prev2Lo (by decide) _ (by push_cast; ring)
  · exact port_hi _ _ _ _ 2 hi hf.prev2 hf.tsLo (by decide) _ (by push_cast; ring)

/-- Closed BabyBear facts the frame and family equations use. -/
theorem inv256 : (256 : ZMod babyBearModulus) * -7864320 = 1 := by decide
theorem clockWrap : (3840 : ZMod babyBearModulus) * 524288 = -1 := by decide

theorem Frame.pc_low (f : Frame) :
    (f.pcLo : ZMod babyBearModulus) + 4 = (f.finalPcLo : Nat) + 65536 * (f.pcCarry : Nat) := by
  have h : ((f.pcLo + 4 : Nat) : ZMod babyBearModulus) =
      (((f.pcLo + 4) % 65536 + 65536 * ((f.pcLo + 4) / 65536) : Nat) : ZMod babyBearModulus) :=
    congrArg _ (Nat.mod_add_div _ _).symm
  push_cast at h
  exact h

theorem Frame.ts_low (f : Frame) :
    (f.tsLo : ZMod babyBearModulus) + 4 = (f.finalTsLo : Nat) + 524288 * (f.tsCarry : Nat) := by
  have h : ((f.tsLo + 4 : Nat) : ZMod babyBearModulus) =
      (((f.tsLo + 4) % 524288 + 524288 * ((f.tsLo + 4) / 524288) : Nat) : ZMod babyBearModulus) :=
    congrArg _ (Nat.mod_add_div _ _).symm
  push_cast at h
  exact h

theorem Frame.pcCarry_bool {f : Frame} (hf : f.Clock) :
    (f.pcCarry : ZMod babyBearModulus) * ((f.pcCarry : ZMod babyBearModulus) - 1) = 0 := by
  have := hf.pcLo
  have : f.pcCarry = 0 ∨ f.pcCarry = 1 := by unfold Frame.pcCarry; omega
  rcases this with h | h <;> rw [h] <;> simp

theorem Frame.tsCarry_bool {f : Frame} (hf : f.Clock) :
    (f.tsCarry : ZMod babyBearModulus) * ((f.tsCarry : ZMod babyBearModulus) - 1) = 0 := by
  have := hf.tsLo
  have : f.tsCarry = 0 ∨ f.tsCarry = 1 := by unfold Frame.tsCarry; omega
  rcases this with h | h <;> rw [h] <;> simp

theorem borrow_bool (prevLo tsLo k : Nat) :
    (borrow prevLo tsLo k : ZMod babyBearModulus) * ((borrow prevLo tsLo k : ZMod babyBearModulus) - 1) = 0 := by
  unfold borrow; split <;> simp

theorem Frame.pc_high (f : Frame) :
    (f.finalPcHi : ZMod babyBearModulus) = (f.pcHi : Nat) + (f.pcCarry : Nat) := by
  unfold Frame.finalPcHi; push_cast; ring

/-- Constraint 89: the clock low limb advances by 4 with at most one wrap. -/
theorem Frame.ts_square {f : Frame} (hf : f.Clock) :
    (14745600 : ZMod babyBearModulus) * ((f.tsLo : ZMod babyBearModulus) + 4 - (f.finalTsLo : Nat)) ^ 2 +
      3840 * ((f.tsLo : ZMod babyBearModulus) + 4 - (f.finalTsLo : Nat)) = 0 := by
  have hX : (f.tsLo : ZMod babyBearModulus) + 4 - (f.finalTsLo : Nat) = 524288 * (f.tsCarry : Nat) := by
    linear_combination f.ts_low
  rw [hX]
  linear_combination ((3840 * 524288 - 1) * (f.tsCarry : ZMod babyBearModulus) ^ 2 +
    (f.tsCarry : ZMod babyBearModulus)) * clockWrap + Frame.tsCarry_bool hf

/-- Constraint 90: the high clock limb absorbs the wrap. -/
theorem Frame.ts_high (f : Frame) :
    (f.finalTsHi : ZMod babyBearModulus) - (f.tsHi : Nat) +
      3840 * ((f.tsLo : ZMod babyBearModulus) + 4 - (f.finalTsLo : Nat)) = 0 := by
  unfold Frame.finalTsHi
  push_cast
  linear_combination 3840 * f.ts_low + (f.tsCarry : ZMod babyBearModulus) * clockWrap

theorem Frame.borrow0_bool (f : Frame) :
    (f.borrow0 : ZMod babyBearModulus) * ((f.borrow0 : ZMod babyBearModulus) - 1) = 0 := borrow_bool _ _ _
theorem Frame.borrow1_bool (f : Frame) :
    (f.borrow1 : ZMod babyBearModulus) * ((f.borrow1 : ZMod babyBearModulus) - 1) = 0 := borrow_bool _ _ _
theorem Frame.borrow2_bool (f : Frame) :
    (f.borrow2 : ZMod babyBearModulus) * ((f.borrow2 : ZMod babyBearModulus) - 1) = 0 := borrow_bool _ _ _

end Airbender.UnifiedReduced.Completeness
