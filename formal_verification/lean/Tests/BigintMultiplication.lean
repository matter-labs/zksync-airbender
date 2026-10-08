import Airbender.Review.Bigint.Theorems

namespace Tests.BigintMultiplication
open Airbender Bigint.Multiplication.Proofs
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem incorrectLowByteRejected (w : Nat → ZMod babyBearModulus)
    (source : w 5 = 65535) (wrong : w 99 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  have low := (source_low_bytes (by decide) row 0).1
  have sourceValue : (65535 : ZMod babyBearModulus).val = 65535 := by decide
  norm_num [Bigint.Variables.leftLimbs, source, wrong, sourceValue, babyBearModulus] at low
  exact (by decide : (0 : ZMod babyBearModulus) ≠ 255) low

theorem oversizedCarryRejected (w : Nat → ZMod babyBearModulus) (i : Fin 31)
    (oversized : 8192 ≤ (carry w i).val) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  have bound := carry_bounded (by decide) row i
  omega

/-- The paired nine-bit query also ranges its second carry, not just its first. -/
theorem pairedCarryRejected (w : Nat → ZMod babyBearModulus)
    (oversized : 512 ≤ (carry w 30).val) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  have bound := carry_ranges (by decide) row 30
  change (carry w 30).val < 512 at bound
  omega

theorem lowProductOverflowRejected
    (setup : Table (ZMod babyBearModulus) (fields 3)) (w : Nat → ZMod babyBearModulus)
    (selected : w 62 = 1 ∨ w 63 = 1) (oversized : 65536 ≤ (w 131).val) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints setup) := by
  intro row
  have bound := product_ranges (by decide) row selected 0
  simp only [Arithmetic.limbBase, Fin.val_zero, Nat.add_zero] at bound
  omega

theorem maximalLimbBytes :
    (255 : ZMod babyBearModulus).val < 256 ∧
      (65535 : ZMod babyBearModulus).val / 256 < 256 ∧
      (65535 : ZMod babyBearModulus) = 255 +
        256 * (((65535 : ZMod babyBearModulus).val / 256 : Nat) : ZMod babyBearModulus) :=
  limb_bytes (by decide) (by decide)

def fiveTimesSevenRow (high carryFlag : Bool) : Nat → ZMod babyBearModulus := fun column =>
  if column = 0 ∨ column = 212 ∨ column = 214 ∨ column = 215 then 1
  else if column = 55 then (if high then 16 else 8) + 64 * carryFlag.toNat
  else if column = 62 then if high then 0 else 1
  else if column = 63 then if high then 1 else 0
  else if column = 65 then carryFlag.toNat
  else if column = 5 ∨ column = 99 then 5
  else if column = 39 ∨ column = 115 then 7
  else if column = 131 ∨ column = 163 ∨ column = 194 then 35
  else if column = 7 then if high then 0 else 35
  else 0

/-- A complete nonzero native witness for both halves and both incoming carry
    values exercises all multiplication equations and lookup regions. -/
theorem fiveTimesSevenSatisfies (high carryFlag : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (fiveTimesSevenRow high carryFlag))
      (Bigint.importedConstraints Bigint.setupTable) := by
  cases high <;> cases carryFlag
  all_goals simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, fiveTimesSevenRow, Lookup.Contains, Table.toRaw,
    fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (refine ⟨⟨0, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])
    | (refine ⟨⟨262144, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])
    | (refine ⟨⟨1310720, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])
    | (refine ⟨⟨1312768, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])
    | (refine ⟨⟨1316864, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])
    | (refine ⟨⟨1325056, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])
    | (refine ⟨⟨1325061, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])
    | (refine ⟨⟨1325063, by decide⟩, ?_⟩; norm_num [Bigint.setupTable, Bigint.setupRow])

-- (2^256 - 1) * 2: low half is 2^256 - 2, high half is one.
def overflowRow : Nat → ZMod babyBearModulus := fun column =>
  if column = 0 ∨ column = 57 ∨ column = 62 ∨ column = 147 ∨ column = 179 ∨
      column = 210 ∨ column = 211 ∨ column = 213 then 1
  else if column = 55 then 8
  else if column = 131 ∨ column = 194 ∨ column = 7 then 65534
  else if column ∈ [5, 6, 9, 10, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30, 33, 34] ∨ column ∈ [8, 11, 12, 15, 16, 19, 20, 23, 24, 27, 28, 31, 32, 35, 36] ∨
      (132 ≤ column ∧ column ≤ 146) ∨ (195 ≤ column ∧ column ≤ 209) then 65535
  else if 99 ≤ column ∧ column ≤ 114 then 255
  else if column = 39 ∨ column = 115 then 2
  else if column = 163 then 131070
  else if 164 ≤ column ∧ column ≤ 178 then 131071
  else 0

theorem overflowSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment overflowRow)
      (Bigint.importedConstraints Bigint.setupTable) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, overflowRow, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (exact ⟨⟨0, by decide⟩, by decide⟩)
    | (exact ⟨⟨512, by decide⟩, by decide⟩)
    | (exact ⟨⟨262144, by decide⟩, by decide⟩)
    | (exact ⟨⟨263168, by decide⟩, by decide⟩)
    | (exact ⟨⟨1310720, by decide⟩, by decide⟩)
    | (exact ⟨⟨1310721, by decide⟩, by decide⟩)
    | (exact ⟨⟨1312768, by decide⟩, by decide⟩)
    | (exact ⟨⟨1312769, by decide⟩, by decide⟩)
    | (exact ⟨⟨1316864, by decide⟩, by decide⟩)
    | (exact ⟨⟨1316865, by decide⟩, by decide⟩)
    | (exact ⟨⟨1325056, by decide⟩, by decide⟩)
    | (exact ⟨⟨1325058, by decide⟩, by decide⟩)
    | (exact ⟨⟨1390591, by decide⟩, by decide⟩)

def smallWord (value : Nat) : Vector Nat 16 :=
  Vector.ofFn fun i => if i.val = 0 then value else 0

/-- The public claim applies to complete native witnesses, for both halves and
    both incoming carry values. -/
theorem fiveTimesSevenSoundness (high carryFlag : Bool) :
    Bigint.Multiplication.spec
      ⟨if high then .high else .low, smallWord 5, smallWord 7⟩
      ⟨smallWord (if high then 0 else 35), ⟨0, 0⟩⟩ := by
  apply Bigint.Multiplication.soundness _ _ (fiveTimesSevenRow high carryFlag)
  refine ⟨fiveTimesSevenSatisfies high carryFlag, ?_⟩
  constructor
  · cases high <;> rfl
  · intro i; cases high <;> cases carryFlag <;> fin_cases i <;> decide
  · intro i; cases high <;> cases carryFlag <;> fin_cases i <;> decide
  · intro i; cases high <;> cases carryFlag <;> fin_cases i <;> decide
  · cases high <;> rfl

theorem missingOverflowRejected (w : Nat → ZMod babyBearModulus)
    (selected : w 62 = 1) (nonzeroHigh : w 210 = 1) (wrongFlag : w 57 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  have control := (native_control (by decide) .low row selected).1
  have nonzero : w 210 ≠ 0 := by rw [nonzeroHigh]; decide
  have impossible : (0 : ZMod babyBearModulus) = 1 := by
    simpa only [wrongFlag, nonzero, ↓reduceIte] using control
  exact (by decide : (0 : ZMod babyBearModulus) ≠ 1) impossible

end Tests.BigintMultiplication
