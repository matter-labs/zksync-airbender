import Airbender.Proofs.Arithmetic.BooleanExpression
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment

set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/- Check the small imported assertion trees once. Soundness proofs can then
   use their scalar semantics without expanding the complete constraint list. -/
namespace Airbender.Blake2Round.Proofs.NativeBooleanBindings

theorem column_expression {p : Nat} [Fact p.Prime] (call : Fin 4) (slot : Fin 4) :
    (FlatOperation.constraints (importedConstraints (setupTable (p := p)))).get
      ⟨NativeLayout.columnBooleanAssertion call slot, by
        rw [constraint_count]; have := call.isLt; have := slot.isLt
        dsimp [NativeLayout.columnBooleanAssertion]; omega⟩ =
      Arithmetic.nativeBooleanExpression (p := p) (NativeLayout.columnBooleanColumns call)[slot] := by
  fin_cases call <;> fin_cases slot <;> rfl

theorem diagonal_expression {p : Nat} [Fact p.Prime] (call : Fin 4) (slot : Fin 2) :
    (FlatOperation.constraints (importedConstraints (setupTable (p := p)))).get
      ⟨NativeLayout.diagonalBooleanAssertion call slot, by
        rw [constraint_count]; have := call.isLt; have := slot.isLt
        dsimp [NativeLayout.diagonalBooleanAssertion]; omega⟩ =
      Arithmetic.nativeBooleanExpression (p := p) (426 + 30 * call.val + 3 * slot.val) := by
  fin_cases call <;> fin_cases slot <;> rfl

theorem diagonal_first_c_read {p : Nat} [Fact p.Prime]
    (call : Fin 4) (slot : Fin 2) (w : Nat → ZMod p) :
    (diagonalFrame call w).cCarries[(slot.castLE (by decide) : Fin 4)] =
      w (426 + 30 * call.val + 3 * slot.val) := by
  fin_cases slot <;>
    simp [diagonalFrame, NativeLayout.Layout.read, NativeLayout.Location.read,
      NativeLayout.diagonal] <;> congr 1 <;> omega

end Airbender.Blake2Round.Proofs.NativeBooleanBindings
