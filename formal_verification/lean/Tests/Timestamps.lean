import Airbender.Proofs.Trace.Claims

namespace Tests.Timestamps
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

-- An active zero-operand ADD row; previous register writes are at timestamp zero.
private def row (clock : Nat) (v : Nat) : ZMod babyBearModulus :=
  if v = 2 then clock
  else if v = 21 then ((clock + 4) % Trace.timestampBase : Nat)
  else if v = 22 then ((clock + 4) / Trace.timestampBase : Nat)
  else if v = 4 ∨ v = 7 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else if v = 19 then 4 else 0

private theorem normal_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row 4)) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row, Trace.timestampBase]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, row, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, Arithmetic.limbBase, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, row, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, Arithmetic.limbBase, babyBearModulus])
    | norm_num [babyBearModulus]

private theorem rollover_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row 524284)) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row, Trace.timestampBase]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, row, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, Arithmetic.limbBase, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, row, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, Arithmetic.limbBase, babyBearModulus])
    | norm_num [babyBearModulus]
  all_goals decide

private theorem input_bounds (clock : Nat) (bounded : clock < 524288) (aligned : clock % 4 = 0) :
    Trace.ClockInputs AddSub.importedConstraintsTraceColumns (row clock) := by
  constructor
  · change ((clock : ZMod babyBearModulus).val < Trace.timestampBase) ∧ _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show clock < babyBearModulus by unfold babyBearModulus; omega)]
    exact ⟨bounded, by norm_num [Trace.decodeTimestamp, AddSub.importedConstraintsTraceColumns, row, Trace.timestampBase, ZMod.val_ofNat, babyBearModulus]⟩
  · change (clock : ZMod babyBearModulus).val % 4 = 0
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show clock < babyBearModulus by unfold babyBearModulus; omega)]
    exact aligned
  · intro port member
    simp [AddSub.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl
    all_goals constructor <;> norm_num [Trace.decodeTimestamp, AddSub.importedConstraintsTraceColumns, row, Trace.timestampBase, ZMod.val_ofNat, babyBearModulus]

theorem normal_effects : Trace.ClockEffects AddSub.importedConstraintsTraceColumns (row 4) :=
  Trace.Proofs.addSub_clock (by decide) (by decide) normal_satisfies (input_bounds _ (by decide) (by decide))

theorem rollover_effects : Trace.ClockEffects AddSub.importedConstraintsTraceColumns (row 524284) :=
  Trace.Proofs.addSub_clock (by decide) (by decide) rollover_satisfies (input_bounds _ (by decide) (by decide))

/-- Changing the previous-write timestamp to the access time is rejected by the
    imported comparison queries, even with the correct arithmetic row. -/
theorem equal_previous_rejected : ¬ FlatOperation.ConstraintsHoldFlat
    (Verification.environment (fun v => if v = 23 then 4 else row 4 v)) AddSub.clockConstraints := by
  intro h
  have effects := Trace.Proofs.addSub_clock (by decide) (by decide) h (by
    constructor
    · constructor <;> decide
    · decide
    · intro port member
      simp [AddSub.importedConstraintsTraceColumns] at member
      rcases member with rfl | rfl | rfl
      all_goals constructor <;> norm_num [Trace.decodeTimestamp, AddSub.importedConstraintsTraceColumns, row, Trace.timestampBase, ZMod.val_ofNat, ZMod.val_natCast, Arithmetic.limbBase, babyBearModulus])
  have order := effects.accesses ⟨0, #v[23, 24], 42, none⟩ (by simp [AddSub.importedConstraintsTraceColumns])
  change 4 < 4 ∧ _ at order
  omega

/-- The first value outside the 19-bit table is rejected. -/
theorem oversized_limb_rejected : ¬ (Trace.timestampLookup
    (Expression.const (524288 : ZMod babyBearModulus))).Contains
      (Verification.environment (fun _ => 0)) := by
  intro h
  have bound := Trace.Proofs.range_bound h
  norm_num [Expression.eval, Trace.timestampBase, ZMod.val_ofNat, babyBearModulus] at bound

end Tests.Timestamps
