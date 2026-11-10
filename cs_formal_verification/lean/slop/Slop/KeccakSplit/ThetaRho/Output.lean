module
public import Slop.KeccakSplit.ThetaRho.Shift
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/- The written state limbs of a theta/rho row: each is the flag-selected sum of the
   rho output bytes, built from the split fragments (ported from PR #585's
   SplitThetaOutputEquations). -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

/-- Output byte `digit` of a lane rotated left by `left`: the low fragment of its source
    byte plus the high fragment of the previous one. -/
noncomputable def outputByte (w : Nat → ZMod babyBearModulus) (lane : Fin 5) (left : Fin 64)
    (digit : Fin 8) : ZMod babyBearModulus :=
  fragmentByte w false lane ⟨(digit.val + 8 - left.val / 8) % 8, Nat.mod_lt _ (by decide)⟩ +
    if left.val % 8 = 0 then 0
    else fragmentByte w true lane ⟨(digit.val + 7 - left.val / 8) % 8, Nat.mod_lt _ (by decide)⟩

/-- Written limb `limb` of lane `lane` if column `column` is the call's. -/
noncomputable def outputLimbExpression (w : Nat → ZMod babyBearModulus) (column lane : Fin 5)
    (limb : Fin 4) : ZMod babyBearModulus :=
  outputByte w lane (Call.rotations[column][lane]) ⟨2 * limb.val, by omega⟩ +
    256 * outputByte w lane (Call.rotations[column][lane]) ⟨2 * limb.val + 1, by omega⟩

theorem rot_0_0 : (Call.rotations[0][0]).val = 0 := by rfl
theorem rot_0_1 : (Call.rotations[0][1]).val = 36 := by rfl
theorem rot_0_2 : (Call.rotations[0][2]).val = 3 := by rfl
theorem rot_0_3 : (Call.rotations[0][3]).val = 41 := by rfl
theorem rot_0_4 : (Call.rotations[0][4]).val = 18 := by rfl
theorem rot_1_0 : (Call.rotations[1][0]).val = 1 := by rfl
theorem rot_1_1 : (Call.rotations[1][1]).val = 44 := by rfl
theorem rot_1_2 : (Call.rotations[1][2]).val = 10 := by rfl
theorem rot_1_3 : (Call.rotations[1][3]).val = 45 := by rfl
theorem rot_1_4 : (Call.rotations[1][4]).val = 2 := by rfl
theorem rot_2_0 : (Call.rotations[2][0]).val = 62 := by rfl
theorem rot_2_1 : (Call.rotations[2][1]).val = 6 := by rfl
theorem rot_2_2 : (Call.rotations[2][2]).val = 43 := by rfl
theorem rot_2_3 : (Call.rotations[2][3]).val = 15 := by rfl
theorem rot_2_4 : (Call.rotations[2][4]).val = 61 := by rfl
theorem rot_3_0 : (Call.rotations[3][0]).val = 28 := by rfl
theorem rot_3_1 : (Call.rotations[3][1]).val = 55 := by rfl
theorem rot_3_2 : (Call.rotations[3][2]).val = 25 := by rfl
theorem rot_3_3 : (Call.rotations[3][3]).val = 21 := by rfl
theorem rot_3_4 : (Call.rotations[3][4]).val = 56 := by rfl
theorem rot_4_0 : (Call.rotations[4][0]).val = 27 := by rfl
theorem rot_4_1 : (Call.rotations[4][1]).val = 20 := by rfl
theorem rot_4_2 : (Call.rotations[4][2]).val = 39 := by rfl
theorem rot_4_3 : (Call.rotations[4][3]).val = 8 := by rfl
theorem rot_4_4 : (Call.rotations[4][4]).val = 14 := by rfl

theorem constraint_count :
    (FlatOperation.constraints (ThetaRho.importedConstraints
      (ThetaRho.setup (p := babyBearModulus)))).length = 35 := by rfl

/-- Fragment columns of the XOR-and-split queries. -/
theorem fragment_col (w : Nat → ZMod babyBearModulus) (high : Bool) (lane : Fin 5) (digit : Fin 8) :
    fragmentByte w high lane digit = w (93 + 20 * lane.val + 2 * digit.val + if high then 1 else 0) := by
  simp only [fragmentByte, row_entry, query]
  cases high <;> fin_cases lane <;> fin_cases digit <;> (op_index) <;>
    simp [Expression.eval, Verification.environment]

theorem output_equation {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) (limb : Fin 4) :
    limbOf w true ⟨lane.val, by omega⟩ limb =
      columnFlag w 0 * outputLimbExpression w 0 lane limb +
      columnFlag w 1 * outputLimbExpression w 1 lane limb +
      columnFlag w 2 * outputLimbExpression w 2 lane limb +
      columnFlag w 3 * outputLimbExpression w 3 lane limb +
      columnFlag w 4 * outputLimbExpression w 4 lane limb := by
  have e := Verification.assertion_of_holds (core h)
    ⟨3 + 4 * lane.val + limb.val, by rw [constraint_count]; omega⟩
  simp only [outputLimbExpression, outputByte, fragment_col]
  fin_cases lane <;> fin_cases limb <;> op_index at e <;>
    simp only [Fin.getElem_fin, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod] <;>
    simp only [rot_0_0, rot_0_1, rot_0_2, rot_0_3, rot_0_4, rot_1_0, rot_1_1, rot_1_2, rot_1_3, rot_1_4, rot_2_0, rot_2_1, rot_2_2, rot_2_3, rot_2_4, rot_3_0, rot_3_1, rot_3_2, rot_3_3, rot_3_4, rot_4_0, rot_4_1, rot_4_2, rot_4_3, rot_4_4] <;>
    simp only [limbOf, limbColumn, columnFlag] <;>
    norm_num [Expression.eval, Verification.environment, writeCol] at e ⊢ <;>
    linear_combination -e

theorem selected_output {w : Nat → ZMod babyBearModulus} (h : Holds w) (column lane : Fin 5) (limb : Fin 4)
    (flags : ∀ selected : Fin 5, columnFlag w selected = if selected.val = column.val then 1 else 0) :
    limbOf w true ⟨lane.val, by omega⟩ limb = outputLimbExpression w column lane limb := by
  rw [output_equation h lane limb]
  fin_cases column <;> simp [flags]

end Airbender.Keccak.Split.ThetaRho.Proofs
