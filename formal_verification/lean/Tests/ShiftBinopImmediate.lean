import Airbender.Proofs.ShiftBinop.Ports
import Tests.ShiftBinopTimestamp

namespace Tests.ShiftBinopImmediate
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

-- XORI x1,x0,-1: exercise both packed immediate bytes and the upper sign bytes.
private def row (i : Nat) : ZMod babyBearModulus :=
  if i = 8 ∨ i = 9 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
      i = 52 ∨ i = 53 ∨ i = 57 ∨ i = 58 ∨ i = 66 ∨ i = 67 ∨
      i = 75 ∨ i = 76 ∨ i = 84 ∨ i = 85 then 255
  else if i = 31 ∨ i = 32 then 65535
  else Tests.ShiftBinopTimestamp.assignment false i

theorem constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    Airbender.ShiftBinop.importedConstraints := by
  simp [Airbender.ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row, Tests.ShiftBinopTimestamp.assignment,
    Tests.ShiftBinop.row]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[255, 255, 0, 0, 0, 0, 0, 0, 0, 3] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨256, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨256, by decide⟩ =
           (#v[255, 255, 0, 0, 0, 0, 0, 0, 0, 3] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[0, 255, 255, 0, 0, 0, 0, 0, 0, 4] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨512, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨512, by decide⟩ =
           (#v[0, 255, 255, 0, 0, 0, 0, 0, 0, 4] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)

theorem effective_operand :
    ∀ i : Fin 4, row (25 + i.val) +
      (if i.val = 0 then row 8 else if i.val = 1 then row 9 else row 35) =
      ((SailRV32.Functions.sign_extend (m := 32) (4095#12)).extractLsb'
        (8 * i.val) 8).toNat :=
  Airbender.ShiftBinop.Proofs.binary_immediate_right_bytes (by decide) constraints
    ⟨by decide, by decide⟩ 4 (Or.inl rfl) (by decide) 4095#12
    ⟨by decide, by decide⟩ (by decide)

end Tests.ShiftBinopImmediate
