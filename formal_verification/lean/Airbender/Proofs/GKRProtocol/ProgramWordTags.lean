import Airbender.Proofs.WordMemory
import Airbender.Import.GKRProtocol.Source

namespace Airbender.WordMemory.Proofs
open Airbender.Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- Native arithmetic alone fixes all word-memory selector bits. -/
theorem word_flags_of_assertions {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (arithmetic : ∀ expression ∈ FlatOperation.constraints (importedConstraints rom),
      expression.eval (Verification.environment w) = 0) :
    ∀ i : Fin 8, w (#v[4, 10, 35, 33, 34, 46, 47, 48][i]) = 0 ∨
      w (#v[4, 10, 35, 33, 34, 46, 47, 48][i]) = 1 := by
  intro i
  have flag := arithmetic _ (List.get_mem _
    ⟨(#v[0, 22, 23, 5, 6, 24, 25, 26][i]), by rw [constraint_count]; fin_cases i <;> decide⟩)
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] at flag ⊢
  all_goals first | exact flag | exact flag.imp id Eq.symm

end Airbender.WordMemory.Proofs

namespace Airbender.Compiler
open Airbender Airbender.Compiler
variable [Fact babyBearModulus.Prime]
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- The native word-ROM request cannot select decoder rows. -/
theorem word_helper_not_decoder (setup : Table Source.BaseField (fields 9))
    (w : Nat → Source.BaseField)
    (arithmetic : ∀ expression ∈ FlatOperation.constraints (WordMemory.importedConstraints setup),
      expression.eval (Verification.environment w) = 0) : w 45 ≠ 46 := by
  have r := arithmetic _ (List.get_mem _ ⟨9, by rw [WordMemory.constraint_count]; decide⟩)
  have active := arithmetic _ (List.get_mem _ ⟨16, by rw [WordMemory.constraint_count]; decide⟩)
  have tag := arithmetic _ (List.get_mem _ ⟨17, by rw [WordMemory.constraint_count]; decide⟩)
  simp [WordMemory.importedConstraints, FlatOperation.constraints, _root_.Expression.eval, Verification.environment] at r active tag
  have copyR : w 37 = w 35 := by linear_combination r
  have copyA : w 44 = w 4 := by linear_combination active
  have notTag : w 45 ≠ 46 := by
    intro wrong
    rw [copyR, copyA, wrong] at tag
    have fa : w 4 = 0 ∨ w 4 = 1 := by simpa using WordMemory.Proofs.word_flags_of_assertions arithmetic 0
    have fb : w 35 = 0 ∨ w 35 = 1 := by simpa using WordMemory.Proofs.word_flags_of_assertions arithmetic 2
    rcases fa with a | a
    all_goals rcases fb with b | b
    all_goals norm_num [a, b] at tag
    all_goals have bad := congrArg ZMod.val tag
    all_goals norm_num [ZMod.val_ofNat, Source.BaseField, babyBearModulus] at bad
  exact notTag

end Airbender.Compiler
