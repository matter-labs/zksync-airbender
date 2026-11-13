module
public import Proven.UnifiedReduced.WordMemory
public import Human.Circuits.UnifiedReduced.Tables.Setup
public import Proven.ByteTables
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem word_rom_selection [Fact p.Prime] (hp : 131072 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} (store : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 28 = if store then 0 else 1) (other : w 29 = if store then 1 else 0) :
    w 54 = (if (w (if store then 45 else 39)).val < 64 then 1 else 0) ∧
      (store = true → 64 ≤ (w 45).val) := by
  have index := Verification.assertion_of_holds holds ⟨if store then 35 else 34,
    by rw [constraint_count]; split <;> decide⟩
  have residue := Verification.assertion_of_holds holds ⟨36, by rw [constraint_count]; decide⟩
  op_index at residue
  have range := Verification.lookup_of_holds holds ⟨10, by rw [lookup_count]; decide⟩
  op_index at range
  replace range := Verification.range16_bound range
  have indexed : w 58 = w (if store then 45 else 39) := by
    cases store
    all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at index
    all_goals op_index at index
    all_goals simp [Expression.eval, Verification.environment, selected, other] at index
    all_goals simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals linear_combination index
  have equation : w 80 + 64 = w (if store then 45 else 39) + 65536 * w 54 := by
    cases store
    all_goals simp [Expression.eval, Verification.environment, selected, other] at residue
    all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at indexed ⊢
    all_goals linear_combination residue + indexed
  have range : (w 80).val < 65536 := by simpa [Expression.eval, Verification.environment, limbBase] using range
  have upper : (w (if store then 45 else 39)).val < 65536 := by
    cases store
    · have bound := Verification.lookup_of_holds holds ⟨7, by rw [lookup_count]; decide⟩
      op_index at bound
      replace bound := Verification.range16_bound bound
      simpa [Expression.eval, Verification.environment, limbBase] using bound
    · have bound := Verification.lookup_of_holds holds ⟨9, by rw [lookup_count]; decide⟩
      op_index at bound
      replace bound := Verification.range16_bound bound
      simpa [Expression.eval, Verification.environment, limbBase] using bound
  have classify : w 54 = (if (w (if store then 45 else 39)).val < 64 then 1 else 0) := by
    have flag := local_flags holds 22
    change w 54 = 0 ∨ w 54 = 1 at flag
    rcases flag with zero | one
    · rw [zero] at equation
      have equal : (w 80).val + 64 = (w (if store then 45 else 39)).val := by
        apply bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega)
        simpa only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val, mul_zero, add_zero] using equation
      simp [zero, show ¬(w (if store then 45 else 39)).val < 64 by omega]
    · rw [one] at equation
      have equal : (w 80).val + 64 = (w (if store then 45 else 39)).val + 65536 := by
        apply bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega)
        simpa only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val, mul_one] using equation
      simp [one, show (w (if store then 45 else 39)).val < 64 by omega]
  refine ⟨classify, ?_⟩
  intro storeMode
  have readonly := Verification.assertion_of_holds holds ⟨38, by rw [constraint_count]; decide⟩
  op_index at readonly
  simp [Expression.eval, Verification.environment, other, storeMode] at readonly
  change w 54 = 0 at readonly
  rw [storeMode] at classify
  change w 54 = (if (w 45).val < 64 then 1 else 0) at classify
  by_contra below
  have small : (w 45).val < 64 := by omega
  rw [ite_eq_left small, readonly] at classify
  exact zero_ne_one classify

end Airbender.UnifiedReduced.Proofs
