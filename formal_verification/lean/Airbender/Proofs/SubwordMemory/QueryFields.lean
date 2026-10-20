import Airbender.Proofs.SubwordMemory.Controls
import Airbender.Proofs.SubwordMemory.NativeResolution

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
/-- Native rom inputs and outputs survive multiplexing without assuming
    any intermediate limb, query key or table result. -/
theorem rom_fields (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 0) (ram : w 26 = 0) :
    w 52 = 536870912 * (w 19 - w 22 + 65536 * w 27) ∧
    w 53 = w 41 ∧
    w 54 = w 42 ∧
    w 56 = w 43 + 65536 * w 22 + 262144 * w 11 ∧
    w 57 = w 44 ∧
    w 58 = w 45 := by
  obtain ⟨tag0,tag1⟩ := rom_tags holds store ram
  have q26 := assertion_of_holds holds ⟨26, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q26
  have q27 := assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q27
  have q28 := assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q28
  have q29 := assertion_of_holds holds ⟨29, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q29
  have q30 := assertion_of_holds holds ⟨30, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q30
  have q31 := assertion_of_holds holds ⟨31, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q31
  have c2 : (4294967294 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c3 : (6442450941 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c4 : (8589934588 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c7 : (15032385529 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c8 : (17179869176 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c17 : (36507221999 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c35 : (75161927645 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c16406 : (35231616712682 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linear_combination (norm := (ring_nf; simp only [c3,c4,c8,c35,c16406,mul_zero,add_zero,sub_zero])) -q26
  · linear_combination (norm := (ring_nf; simp only [c7,mul_zero])) -q27
  · linear_combination (norm := (ring_nf; simp only [c7,mul_zero])) -q28
  · linear_combination (norm := (ring_nf; simp only [c2,c8,c17,mul_zero,add_zero])) -q29
  · linear_combination (norm := (ring_nf; simp only [c17,mul_zero])) -q30
  · linear_combination (norm := (ring_nf; simp only [c17,mul_zero])) -q31

/-- Native ram inputs and outputs survive multiplexing without assuming
    any intermediate limb, query key or table result. -/
theorem ram_fields (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 0) (ram : w 26 = 1) :
    w 52 = w 46 + 65536 * w 22 + 262144 * w 11 ∧
    w 53 = w 41 ∧
    w 54 = w 42 ∧
    w 56 = 0 ∧
    w 57 = 0 ∧
    w 58 = 0 := by
  obtain ⟨tag0,tag1⟩ := ram_tags holds store ram
  have q26 := assertion_of_holds holds ⟨26, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q26
  have q27 := assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q27
  have q28 := assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q28
  have q29 := assertion_of_holds holds ⟨29, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q29
  have q30 := assertion_of_holds holds ⟨30, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q30
  have q31 := assertion_of_holds holds ⟨31, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q31
  have c2 : (4294967294 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c8 : (17179869176 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c17 : (36507221999 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linear_combination (norm := (ring_nf; simp only [c2,c8,c17,mul_zero,add_zero])) -q26
  · linear_combination (norm := (ring_nf; simp only [c17,mul_zero])) -q27
  · linear_combination (norm := (ring_nf; simp only [c17,mul_zero])) -q28
  · exact q29
  · exact q30
  · exact q31

/-- Native store inputs and outputs survive multiplexing without assuming
    any intermediate limb, query key or table result. -/
theorem store_fields (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 1) :
    w 52 = w 47 + 65536 * w 22 + 262144 * w 11 ∧
    w 53 = w 41 ∧
    w 54 = w 42 ∧
    w 56 = w 32 + 65536 * w 22 + 262144 * w 11 ∧
    w 57 = w 44 ∧
    w 58 = w 45 := by
  obtain ⟨tag0,tag1⟩ := store_tags holds store
  have q26 := assertion_of_holds holds ⟨26, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q26
  have q27 := assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q27
  have q28 := assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag0, tag1] at q28
  have q29 := assertion_of_holds holds ⟨29, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q29
  have q30 := assertion_of_holds holds ⟨30, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q30
  have q31 := assertion_of_holds holds ⟨31, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    store, tag1] at q31
  have c2 : (4294967294 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c3 : (6442450941 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c5 : (10737418235 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c8 : (17179869176 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c9 : (19327352823 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c10 : (21474836470 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c21 : (45097156587 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c27 : (57982058469 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c42 : (90194313174 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · linear_combination (norm := (ring_nf; simp only [c3,c5,c9,c27,c42,mul_zero,add_zero,sub_zero])) -q26
  · linear_combination (norm := (ring_nf; simp only [c8,mul_zero])) -q27
  · linear_combination (norm := (ring_nf; simp only [c8,mul_zero])) -q28
  · linear_combination (norm := (ring_nf; simp only [c2,c10,c21,mul_zero,add_zero])) -q29
  · linear_combination (norm := (ring_nf; simp only [c21,mul_zero])) -q30
  · linear_combination (norm := (ring_nf; simp only [c21,mul_zero])) -q31

end Airbender.SubwordMemory.Proofs
