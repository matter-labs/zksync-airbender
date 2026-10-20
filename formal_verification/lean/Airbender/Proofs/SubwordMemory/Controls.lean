import Airbender.Proofs.SubwordMemory.NativeQueries
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Mersenne31

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

/-- The store control is Boolean in the actual native equations. -/
theorem store_bit (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) : w 12 = 0 ∨ w 12 = 1 := by
  have eq := assertion_of_holds holds ⟨10, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at eq
  have bit : w 12 * (w 12 - 1) = 0 := by linear_combination -eq
  rcases mul_eq_zero.mp bit with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

/-- The separator query is the native fixed lookup, not a supplied RAM flag. -/
theorem separator_query (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    ∃ i : Fin 65536, #v[w 20,w 26,w 27] = (romSeparatorRow i).map Nat.cast := by
  have query := lookup_of_holds holds ⟨11, by rw [lookup_count]; decide⟩
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
    Table.toRaw, romSeparatorTable, Table.fromStatic, StaticTable.toTable,
    Expression.eval, environment, ProvableType.fromElements] using query

/-- Canonical high-address bits determine both separator outputs. -/
theorem separator_values (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    w 26 = (if (w 20).val < 64 then 0 else 1) ∧
    w 27 = ((w 20).val % 64 : Nat) := by
  obtain ⟨i, row⟩ := separator_query holds
  have high := congrArg (fun q => q[0]) row
  have ram := congrArg (fun q => q[1]) row
  have chunk := congrArg (fun q => q[2]) row
  simp [romSeparatorRow] at high ram chunk
  have index : (w 20).val = i.val := by
    rw [high, ZMod.val_natCast_of_lt (by have := i.isLt; change _ < 2147483647; omega)]
  simp only [index]
  exact ⟨by simpa only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using ram, chunk⟩

theorem ram_bit (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) : w 26 = 0 ∨ w 26 = 1 := by
  have same := (separator_values holds).1
  split_ifs at same <;> simp_all

/-- Native stores cannot select the ROM address range. -/
theorem store_requires_ram (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 1) : w 26 = 1 := by
  have eq := assertion_of_holds holds ⟨12, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at eq
  rw [store] at eq
  linear_combination -eq

/-- The subword-size selector is constrained by its native Boolean equation. -/
theorem size_bit (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) : w 24 = 0 ∨ w 24 = 1 := by
  have eq := assertion_of_holds holds ⟨1, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at eq
  have bit : w 24 * (w 24 - 1) = 0 := by linear_combination eq
  rcases mul_eq_zero.mp bit with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

/-- The upper-limb selector is constrained by its native Boolean equation. -/
theorem upper_bit (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) : w 25 = 0 ∨ w 25 = 1 := by
  have eq := assertion_of_holds holds ⟨2, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at eq
  have bit : w 25 * (w 25 - 1) = 0 := by linear_combination eq
  rcases mul_eq_zero.mp bit with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

/-- Both lookup selectors are fixed by the original optimized equations. -/
theorem selector_equations (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    w 55 = 46 - w 26 + 9 * w 12 ∧ w 59 = 45 - 45 * w 26 + 55 * w 12 := by
  have noRom := assertion_of_holds holds ⟨12, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at noRom
  have second := assertion_of_holds holds ⟨13, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at second
  have first := assertion_of_holds holds ⟨14, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at first
  have c17 : (36507221999 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c35 : (75161927645 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c13 : (27917287411 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c10 : (21474836470 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  constructor
  · linear_combination (norm := (ring_nf; simp only [c17,c35,c13,mul_zero,neg_zero,sub_zero])) -45 * first - 46 * second - noRom
  · linear_combination (norm := (ring_nf; simp only [c17,c10,mul_zero,neg_zero,sub_zero])) -45 * second - 45 * noRom

theorem rom_tags (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 0) (ram : w 26 = 0) : w 55 = 46 ∧ w 59 = 45 := by
  have tags := selector_equations holds
  norm_num [store, ram, mersenne31Modulus] at tags ⊢
  exact tags

theorem ram_tags (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 0) (ram : w 26 = 1) : w 55 = 45 ∧ w 59 = 0 := by
  have tags := selector_equations holds
  norm_num [store, ram, mersenne31Modulus] at tags ⊢
  exact tags

theorem store_tags (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 1) : w 55 = 54 ∧ w 59 = 55 := by
  have ram := store_requires_ram holds store
  have tags := selector_equations holds
  norm_num [store, ram, mersenne31Modulus] at tags ⊢
  exact tags

/-- The mixed memory addresses and register/RAM mode complement come from the
    native equations, including the low-address offset subtraction. -/
theorem port_addresses (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    w 30 = (w 19 - w 22) * (1 - w 12) + w 6 * w 12 ∧
    w 31 = w 20 * (1 - w 12) ∧
    w 35 = (w 19 - w 22) * w 12 + w 7 * (1 - w 12) ∧
    w 36 = w 20 * w 12 ∧ w 34 = 1 - w 12 := by
  have lowRead := assertion_of_holds holds ⟨15, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at lowRead
  have highRead := assertion_of_holds holds ⟨16, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at highRead
  have lowWrite := assertion_of_holds holds ⟨17, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at lowWrite
  have highWrite := assertion_of_holds holds ⟨18, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at highWrite
  have mode := assertion_of_holds holds ⟨48, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at mode
  refine ⟨?_,?_,?_,?_,?_⟩
  · linear_combination -lowRead
  · linear_combination -highRead
  · linear_combination -lowWrite
  · linear_combination -highWrite
  · linear_combination -mode

/-- Three distinct native muxes select ROM data, RAM-load data and old store
    data. The selected limb is derived, never supplied as an intermediate read. -/
theorem selected_limbs (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    w 43 = (1 - w 25) * w 41 + w 25 * w 42 ∧
    w 46 = (1 - w 25) * w 32 + w 25 * w 33 ∧
    w 47 = (1 - w 25) * w 37 + w 25 * w 38 := by
  have romLimb := assertion_of_holds holds ⟨19, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at romLimb
  have ramLimb := assertion_of_holds holds ⟨20, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at ramLimb
  have storeLimb := assertion_of_holds holds ⟨21, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at storeLimb
  refine ⟨?_,?_,?_⟩
  · linear_combination -romLimb
  · linear_combination -ramLimb
  · linear_combination -storeLimb

end Airbender.SubwordMemory.Proofs
