import Airbender.Proofs.SubwordMemory.Controls
import Airbender.Review.Circuits.SubwordMemory.ValuesModel

namespace Airbender.SubwordMemory.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

/-- Actual ROM candidate mux, derived after the native selectors. -/
theorem rom_load_candidate (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (load : w 12 = 0) (ram : w 26 = 0) :
    w 60 = w 44 ∧ w 61 = w 45 := by
  obtain ⟨tag0,tag1⟩ := rom_tags holds load ram
  have q32 := assertion_of_holds holds ⟨32,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    load,tag0,tag1] at q32
  have q33 := assertion_of_holds holds ⟨33,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    load,tag0,tag1] at q33
  have c17 : (36507221999 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  have c35 : (75161927645 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  constructor
  · linear_combination (norm := (ring_nf; simp [c17,c35])) -q32
  · linear_combination (norm := (ring_nf; simp [c17,c35])) -q33

/-- Actual RAM candidate mux, derived after the native selectors. -/
theorem ram_load_candidate (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (load : w 12 = 0) (ram : w 26 = 1) :
    w 60 = w 41 ∧ w 61 = w 42 := by
  obtain ⟨tag0,tag1⟩ := ram_tags holds load ram
  have q32 := assertion_of_holds holds ⟨32,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    load,tag0,tag1] at q32
  have q33 := assertion_of_holds holds ⟨33,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    load,tag0,tag1] at q33
  have c17 : (36507221999 : ZMod mersenne31Modulus) = 0 := by decide +kernel
  constructor
  · linear_combination (norm := (ring_nf; simp [c17])) -q32
  · linear_combination (norm := (ring_nf; simp [c17])) -q33

/-- Native masked register writes retain the actual x0 field. Its public
    Boolean decoding is not silently assumed at this local stage. -/
theorem load_write_mask (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (load : w 12 = 0) :
    w 39 = (1 - w 8) * w 60 ∧ w 40 = (1 - w 8) * w 61 := by
  have q34 := assertion_of_holds holds ⟨34,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q34
  have q35 := assertion_of_holds holds ⟨35,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q35
  have q36 := assertion_of_holds holds ⟨36,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q36
  have q37 := assertion_of_holds holds ⟨37,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q37
  rw [load] at q36 q37
  constructor
  · linear_combination -q34 - q36
  · linear_combination -q35 - q37

/-- Both supported x0-flag values give exact writes; these implications
    do not claim that an unchecked decoder field is globally Boolean. -/
theorem load_write_cases (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (load : w 12 = 0) :
    (w 8 = 0 → #v[w 39,w 40] = #v[w 60,w 61]) ∧
    (w 8 = 1 → #v[w 39,w 40] = #v[0,0]) := by
  obtain ⟨low,high⟩ := load_write_mask holds load
  constructor
  · intro zero
    rw [low,high,zero]
    simp
  · intro one
    rw [low,high,one]
    simp

/-- Actual store writes preserve the opposite old limb and select full-word
    source data or the certified clearing/placement sum using native controls. -/
theorem store_write_mux (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 1) :
    w 39 = storeLow w (w 41) (w 44) ∧ w 40 = storeHigh w (w 41) (w 44) := by
  have q22 := assertion_of_holds holds ⟨22,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q22
  have q23 := assertion_of_holds holds ⟨23,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q23
  have q24 := assertion_of_holds holds ⟨24,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q24
  have q25 := assertion_of_holds holds ⟨25,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q25
  have q38 := assertion_of_holds holds ⟨38,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q38
  have q39 := assertion_of_holds holds ⟨39,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at q39
  rw [store] at q38 q39
  have lowMerged : w 48 = (1 - w 25) * (w 41 + w 44) + w 25 * w 37 := by
    linear_combination -q22
  have highMerged : w 49 = w 25 * (w 41 + w 44) + (1 - w 25) * w 38 := by
    linear_combination -q23
  have lowSelected : w 50 = w 24 * w 48 + (1 - w 24) * w 32 := by
    linear_combination -q24
  have highSelected : w 51 = w 24 * w 49 + (1 - w 24) * w 33 := by
    linear_combination -q25
  have low : w 39 = w 50 := by linear_combination -q38
  have high : w 40 = w 51 := by linear_combination -q39
  constructor
  · simpa only [storeLow,lowMerged,lowSelected] using low
  · simpa only [storeHigh,highMerged,highSelected] using high

end Airbender.SubwordMemory.Proofs
