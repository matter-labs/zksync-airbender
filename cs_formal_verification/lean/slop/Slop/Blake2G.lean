module
public import Human.Circuits.Blake2G.Artifact
public import Human.Helpers.Properties
public import Slop.Constraints
public import Slop.Trace.Timestamps
public import Slop.Arithmetic.Chunks
public import Slop.Blake2G.Lookups
public import Slop.Templates
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.Blake2G.Proofs

set_option warningAsError true

/-- Constraints `11 + i`: the Boolean carries and borrows after execute. -/
private theorem flag_shapes {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9))
    (i : Fin 21) :
    (FlatOperation.constraints (importedConstraints setup)).get
      ⟨11 + i.val, by rw [constraint_count]; omega⟩ =
        Templates.flag Variables.booleanColumns[i.val + 1] := by
  fin_cases i <;> op_index <;> rfl

/-- Carries, timestamp borrows and execute are forced to be Boolean by the artifact. -/
theorem local_flags {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 22,
      w Variables.booleanColumns[i] = 0 ∨ w Variables.booleanColumns[i] = 1 := by
  intro i
  by_cases first : i.val = 0
  · have zero := Verification.assertion_of_holds h ⟨0, by rw [constraint_count]; decide⟩
    op_index at zero
    simp only [Expression.eval, Verification.environment] at zero
    push_cast at zero
    have column : Variables.booleanColumns[i] = 0 := by
      simp only [Fin.getElem_fin, first]
      rfl
    rw [column]
    rcases mul_eq_zero.mp zero with one | zero
    · exact Or.inr (by linear_combination one)
    · exact Or.inl zero
  · have column : Variables.booleanColumns[i] = Variables.booleanColumns[i.val - 1 + 1] := by
      simp only [Fin.getElem_fin, Nat.sub_add_cancel (Nat.pos_of_ne_zero first)]
    rw [column]
    exact Templates.flag_bit h (flag_shapes setup ⟨i.val - 1, by omega⟩)

/-- Mixing constraints `8 + i`: the twelve arithmetic carries. -/
private theorem mixing_flag_shapes {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9))
    (i : Fin 12) :
    (FlatOperation.constraints (mixingConstraints setup)).get
      ⟨8 + i.val, by rw [mixing_constraint_count]; omega⟩ =
        Templates.flag Variables.booleanColumns[1 + i.val] := by
  fin_cases i <;> op_index <;> rfl

/-- Only the twelve arithmetic carries are needed by the reusable G proof. -/
theorem mixing_flags {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (mixingConstraints setup)) :
    ∀ i : Fin 12,
      w Variables.booleanColumns[1 + i.val] = 0 ∨ w Variables.booleanColumns[1 + i.val] = 1 :=
  fun i => Templates.flag_bit h (mixing_flag_shapes setup i)

/-- The control register is explicitly confined to its low limb, on reads and writes. -/
theorem control_high_zero {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    w Variables.controlReadHi = 0 ∧ w Variables.controlWriteHi = 0 := by
  have read := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have write := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  op_index at read write
  simp only [Expression.eval, Verification.environment] at read write
  exact ⟨read, write⟩

private theorem aligned_of_scaled_bound {p : Nat} [Fact p.Prime] (hp : 33554432 ≤ p)
    {x : ZMod p} (inverse : 64 * (-31457280 : ZMod p) = 1)
    (bound : ((-31457280 : ZMod p) * x).val < 524288) : x.val % 64 = 0 := by
  have value := Arithmetic.value_of_scaled_range hp (by decide) inverse bound
  rw [value]
  simp

/-- The two imported scaled-range queries force both ABI pointers to be 64-byte aligned.
    The serialized inverse identity is an artifact/field compatibility premise. -/
theorem pointer_alignment {p : Nat} [Fact p.Prime] (hp : 33554432 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w Variables.statePointerLo).val % 64 = 0 ∧
      (w Variables.messagePointerLo).val % 64 = 0 := by
  have state := Verification.lookup_of_holds h ⟨0, by rw [lookup_count]; decide⟩
  have message := Verification.lookup_of_holds h ⟨1, by rw [lookup_count]; decide⟩
  op_index at state message
  replace state := Airbender.Trace.Proofs.range_bound state
  replace message := Airbender.Trace.Proofs.range_bound message
  simp [Expression.eval,
    Verification.environment, Trace.timestampBase] at state message
  exact ⟨aligned_of_scaled_bound hp inverse (by simpa only [neg_mul] using state),
    aligned_of_scaled_bound hp inverse (by simpa only [neg_mul] using message)⟩

end Airbender.Blake2G.Proofs
