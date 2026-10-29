import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Bigint.AdditiveFields

namespace Airbender.Bigint.Additive.Proofs
open Arithmetic

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option warningAsError true

def carryColumn (i : Nat) : Nat := if i = 0 then 65 else 82 + i

theorem native_steps {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} (operation : Operation)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.operations[operation.index] = 1) :
    ∀ i : Fin 16,
      let left := w Variables.leftLimbs[i]
      let right := w Variables.rightLimbs[i]
      let result := w (67 + i.val)
      let incoming := w (carryColumn i.val)
      let outgoing := w (83 + i.val)
      match operation with
      | .add => left + right + incoming = result + 65536 * outgoing
      | .sub => result + right + incoming = left + 65536 * outgoing
      | .reverseSub => result + left + incoming = right + 65536 * outgoing
      | .copy => right + incoming = result + 65536 * outgoing := by
  have flags := selected_operations hp operation.index h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f4 := flags 4
  have f5 := flags 5
  have f6 := flags 6
  intro i
  have gate := Verification.assertion_of_holds h ⟨3 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  cases operation <;> simp [Operation.index, Variables.operations] at f0 f1 f2 f3 f4 f5 f6
  all_goals fin_cases i
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f5, f6] at gate
  all_goals norm_num [Variables.leftLimbs, Variables.rightLimbs, carryColumn]
  all_goals linear_combination gate

theorem native_results {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} (operation : Operation)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.operations[operation.index] = 1) :
    ∀ i : Fin 16, w (194 + i.val) = w (67 + i.val) ∧
      w Variables.writtenLimbs[i] = w (67 + i.val) := by
  have flags := selected_operations hp operation.index h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f4 := flags 4
  have f5 := flags 5
  have f6 := flags 6
  intro i
  have definition := Verification.assertion_of_holds h ⟨51 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  have write := Verification.assertion_of_holds h ⟨67 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  cases operation <;> simp [Operation.index, Variables.operations] at f0 f1 f2 f3 f4 f5 f6
  all_goals fin_cases i
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f3, f4, f5, f6] at definition write
  all_goals norm_num [Variables.writtenLimbs]
  all_goals constructor
  all_goals first | linear_combination definition | linear_combination -write

theorem returned_control {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} (operation : Operation)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.operations[operation.index] = 1) : w 57 = w 98 ∧ w 58 = 0 := by
  have flags := selected_operations hp operation.index h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f4 := flags 4
  have f5 := flags 5
  have f6 := flags 6
  have low := Verification.assertion_of_holds h ⟨89, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨90, by rw [constraint_count]; decide⟩
  cases operation <;> simp [Operation.index, Variables.operations] at f0 f1 f2 f3 f4 f5 f6
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f3, f5, f6] at low high
  all_goals refine ⟨?_, high⟩
  all_goals linear_combination -low

end Airbender.Bigint.Additive.Proofs
