import Airbender.Proofs.Keccak.SplitThetaBytes

namespace Airbender.Keccak.Split.Native.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The complete evaluated fields of one actual native theta/rho query. -/
def thetaQueryRow (cached : Bool) (w : Nat → ZMod babyBearModulus) (index : Fin 50) :
    Vector (ZMod babyBearModulus) 9 :=
  (thetaRhoQueryEntry cached index).map (Expression.eval (Verification.environment w))

/-- The actual native controller selects the original transition and every exact column flag. -/
theorem theta_native_controller_schedule (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .thetaRho ∧
      (thetaQueryRow cached w 9)[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      (thetaQueryRow cached w 9)[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ column : Fin 5, (thetaQueryRow cached w 9)[3 + column.val] =
        if column.val = index.val % 5 then 1 else 0) := by
  apply Fixed.Proofs.theta_rho_controller_table_schedule _ (theta_rho_native_control_query cached w holds)
  cases cached <;>
    dsimp only [thetaRhoQueryEntry, thetaRhoQuery,
      ThetaRho.importedConstraints, ThetaRhoCached.importedConstraints,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment] <;>
    simp [Expression.eval]
  all_goals
    change (@Vector.mk _ 9 _ _)[1] = 1
    simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using active

/-- The actual native slot key retains the complete control word and execute flag. -/
theorem theta_native_slot_key (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (thetaQueryRow cached w 0)[0] = (thetaQueryRow cached w 9)[0] + 2048 * w 0 := by
  cases cached <;>
    dsimp only [thetaQueryRow, thetaRhoQueryEntry, thetaRhoQuery,
      ThetaRho.importedConstraints, ThetaRhoCached.importedConstraints,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring

/-- The two actual native controller queries bind all seven original physical slots. -/
theorem theta_native_slots (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (active : w 0 = 1)
    (index : Fin 361)
    (control : (thetaQueryRow cached w 9)[0] = (controlAt index.val : ZMod babyBearModulus)) :
    ∀ lane : Fin 7, (thetaQueryRow cached w 0)[1 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  apply Fixed.Proofs.theta_rho_slot_table_sound _ (theta_rho_native_slot_query cached w holds) index
  change (thetaQueryRow cached w 0)[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus)
  rw [theta_native_slot_key, control, active, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- An actual native column flag in the complete controller query. -/
def thetaColumnFlag (cached : Bool) (w : Nat → ZMod babyBearModulus) (column : Fin 5) : ZMod babyBearModulus :=
  (thetaQueryRow cached w 9)[3 + column.val]'(by have := column.isLt; omega)

/-- The actual native byte shift is the original rho offset selected by the five flags. -/
theorem theta_rotation_shift_equation (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 5) :
    thetaRotationShift cached w lane =
      ((Call.rotations[0][lane].val % 8 : Nat) : ZMod babyBearModulus) * thetaColumnFlag cached w 0 +
      ((Call.rotations[1][lane].val % 8 : Nat) : ZMod babyBearModulus) * thetaColumnFlag cached w 1 +
      ((Call.rotations[2][lane].val % 8 : Nat) : ZMod babyBearModulus) * thetaColumnFlag cached w 2 +
      ((Call.rotations[3][lane].val % 8 : Nat) : ZMod babyBearModulus) * thetaColumnFlag cached w 3 +
      ((Call.rotations[4][lane].val % 8 : Nat) : ZMod babyBearModulus) * thetaColumnFlag cached w 4 := by
  cases cached <;> fin_cases lane <;>
    dsimp only [thetaRotationShift, thetaColumnFlag, thetaQueryRow, thetaRhoQueryEntry, thetaRhoQuery,
      ThetaRho.importedConstraints, ThetaRhoCached.importedConstraints,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment, Call.rotations]

/-- Exact native column flags select the unchanged original rho shift. -/
theorem theta_rotation_shift_selected (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    thetaRotationShift cached w lane =
      ((Call.rotations[column][lane].val % 8 : Nat) : ZMod babyBearModulus) := by
  rw [theta_rotation_shift_equation]
  fin_cases column <;> simp [flags]

/-- The canonical native shift equals the selected original rho offset modulo eight. -/
theorem theta_rotation_shift_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    (thetaRotationShift cached w lane).val = Call.rotations[column][lane].val % 8 := by
  rw [theta_rotation_shift_selected cached w column lane flags]
  exact ZMod.val_natCast_of_lt (lt_trans (Nat.mod_lt _ (by decide : 0 < 8)) (by decide))

end Airbender.Keccak.Split.Native.Proofs
