import Slop.KeccakSplit.ThetaRho.Inputs

/- The theta/rho column flags select the rho shift of each lane (ported from PR #585's
   SplitThetaControllerQuery). -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

/-- The controller's flag for column `column` of the call. -/
def columnFlag (w : Nat → ZMod babyBearModulus) (column : Fin 5) : ZMod babyBearModulus :=
  w (84 + column.val)

theorem rotation_shift_equation (w : Nat → ZMod babyBearModulus) (lane : Fin 5) :
    rotationShift w lane =
      ((Call.rotations[0][lane].val % 8 : Nat) : ZMod babyBearModulus) * columnFlag w 0 +
      ((Call.rotations[1][lane].val % 8 : Nat) : ZMod babyBearModulus) * columnFlag w 1 +
      ((Call.rotations[2][lane].val % 8 : Nat) : ZMod babyBearModulus) * columnFlag w 2 +
      ((Call.rotations[3][lane].val % 8 : Nat) : ZMod babyBearModulus) * columnFlag w 3 +
      ((Call.rotations[4][lane].val % 8 : Nat) : ZMod babyBearModulus) * columnFlag w 4 := by
  simp only [rotationShift, row_entry, query]
  fin_cases lane <;> (op_index) <;>
    norm_num [Expression.eval, Verification.environment, Call.rotations, columnFlag]

theorem rotation_shift_selected (w : Nat → ZMod babyBearModulus) (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    rotationShift w lane = ((Call.rotations[column][lane].val % 8 : Nat) : ZMod babyBearModulus) := by
  rw [rotation_shift_equation]
  fin_cases column <;> simp [flags]

theorem rotation_shift_value (w : Nat → ZMod babyBearModulus) (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    (rotationShift w lane).val = Call.rotations[column][lane].val % 8 := by
  rw [rotation_shift_selected w column lane flags]
  exact ZMod.val_natCast_of_lt (lt_trans (Nat.mod_lt _ (by decide : 0 < 8)) (by decide))

end Airbender.Keccak.Split.ThetaRho.Proofs
