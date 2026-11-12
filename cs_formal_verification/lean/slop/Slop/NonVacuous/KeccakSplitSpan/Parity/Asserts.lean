module
public import Slop.NonVacuous.KeccakSplitSpan.Parity.Honest
public import Slop.NonVacuous.SpanTactics
public import Slop.KeccakSplit.ColumnParity.OpIndex

@[expose] public section

/-! The 20 imported assertions of a column-parity row hold for the honest assignment of valid inputs: the active
    flag, the zero high limbs of x10, the three non-iota bytes and the unchanged third limb of the first lane, and
    the fourteen borrow flags. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Parity
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

variable {p : Nat} [Fact p.Prime]

theorem asserts (x : RowInput) (setup : Table (ZMod p) (fields 8)) :
    ∀ i (h : i < (FlatOperation.constraints (ColumnParity.importedConstraints setup)).length),
      ((FlatOperation.constraints (ColumnParity.importedConstraints setup)).get ⟨i, h⟩).eval
        (Verification.environment (assignment x)) = 0 := by
  intro i h
  have size : i < 20 := by
    have count : (FlatOperation.constraints (ColumnParity.importedConstraints setup)).length = 20 := by rfl
    omega
  interval_cases i <;> op_index
  · simp only [Expression.eval, Verification.environment, honest_column]
    push_cast
    ring
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · cast_identity p (show x.limb 0 1 % 256 = nib (out x 1) 0 + 16 * nib (out x 1) 1 by
      simp only [out, nib, Nat.reducePow]
      omega)
  · cast_identity p (show x.limb 0 3 % 256 = nib (out x 3) 0 + 16 * nib (out x 3) 1 by
      simp only [out, nib, Nat.reducePow]
      omega)
  · cast_identity p (show x.limb 0 2 = out x 2 from rfl)
  -- the fourteen borrow flags (columns 125 + 3 j) hold 1
  all_goals exact flag_eval (n := 1) rfl le_rfl

end Airbender.NonVacuous.KeccakSplitSpan.Parity
