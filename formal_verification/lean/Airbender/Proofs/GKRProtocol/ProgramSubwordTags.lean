import Airbender.Proofs.SubwordMemory
import Airbender.Import.GKRProtocol.Source

namespace Airbender.SubwordMemory.Proofs
open Airbender.Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- Native arithmetic alone fixes all subword selector bits. -/
theorem subword_flags_of_assertions {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (arithmetic : ∀ expression ∈ FlatOperation.constraints (importedConstraints setup),
      expression.eval (Verification.environment w) = 0) :
    ∀ i : Fin 12, w (#v[4, 10, 11, 12, 35, 36, 37, 38, 41, 62, 63, 64][i]) = 0 ∨
      w (#v[4, 10, 11, 12, 35, 36, 37, 38, 41, 62, 63, 64][i]) = 1 := by
  intro i
  have flag := arithmetic _ (List.get_mem _
    ⟨(#v[0, 34, 35, 36, 37, 38, 4, 6, 39, 40, 41, 42][i]), by rw [constraint_count]; fin_cases i <;> decide⟩)
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] at flag ⊢
  all_goals first | exact flag | exact flag.imp id Eq.symm

end Airbender.SubwordMemory.Proofs

namespace Airbender.Compiler
open Airbender Airbender.Compiler
variable [Fact babyBearModulus.Prime]
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- Native helper tags cannot select decoder rows. This uses no lookup result. -/
theorem subword_helper_not_decoder (setup : Table Source.BaseField (fields 9))
    (w : Nat → Source.BaseField)
    (arithmetic : ∀ expression ∈ FlatOperation.constraints (SubwordMemory.importedConstraints setup),
      expression.eval (Verification.environment w) = 0) : w 61 ≠ 46 := by
  have tag := arithmetic _ (List.get_mem _ ⟨27, by rw [SubwordMemory.constraint_count]; decide⟩)
  have enabled := arithmetic _ (List.get_mem _ ⟨28, by rw [SubwordMemory.constraint_count]; decide⟩)
  have outTag := arithmetic _ (List.get_mem _ ⟨29, by rw [SubwordMemory.constraint_count]; decide⟩)
  simp [SubwordMemory.importedConstraints, FlatOperation.constraints, _root_.Expression.eval, Verification.environment] at tag enabled outTag
  have enabledEq : w 60 = w 4 := by linear_combination enabled
  rw [enabledEq] at outTag
  have tagEq : w 61 = w 4 * (w 41 * (1 - w 11) * 44 + w 41 * w 11 * 45 +
      (1 - w 10 - w 41) * (1 - w 11) * 42 + (1 - w 10 - w 41) * w 11 * 43 +
      w 10 * w 11 * 29) := by linear_combination w 4 * tag + outTag
  have notTag : w 61 ≠ 46 := by
    intro wrong
    rw [wrong] at tagEq
    have fx : w 4 = 0 ∨ w 4 = 1 := by simpa using SubwordMemory.Proofs.subword_flags_of_assertions arithmetic 0
    have fy : w 10 = 0 ∨ w 10 = 1 := by simpa using SubwordMemory.Proofs.subword_flags_of_assertions arithmetic 1
    have fz : w 11 = 0 ∨ w 11 = 1 := by simpa using SubwordMemory.Proofs.subword_flags_of_assertions arithmetic 2
    have ft : w 41 = 0 ∨ w 41 = 1 := by simpa using SubwordMemory.Proofs.subword_flags_of_assertions arithmetic 8
    rcases fx with x | x
    all_goals rcases fy with y | y
    all_goals rcases fz with z | z
    all_goals rcases ft with t | t
    all_goals norm_num [x, y, z, t] at tagEq
    all_goals have bad := congrArg ZMod.val tagEq
    all_goals norm_num [ZMod.val_ofNat, Source.BaseField, babyBearModulus] at bad
  exact notTag

end Airbender.Compiler
