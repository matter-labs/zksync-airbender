import Airbender.Proofs.ReducedMachine.NativeSelectors
import Airbender.Proofs.ReducedMachine.NativeQueries

namespace Airbender.ReducedMachine.NativeShiftRoutingProofs
open Verification Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem field100 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 100 = w 47 := by
  have equation := assertion_of_holds holds ⟨82,by change 82 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31] at equation
  linear_combination -equation

private theorem field101 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 101 = w 64 := by
  have equation := assertion_of_holds holds ⟨83,by change 83 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31] at equation
  linear_combination -equation

private theorem field102 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 102 = w 65 := by
  have equation := assertion_of_holds holds ⟨84,by change 84 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31] at equation
  linear_combination -equation

private theorem field103 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 103 = 47 := by
  have equation := assertion_of_holds holds ⟨85,by change 85 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f24,f25,f27,f29,f31] at equation
  linear_combination -equation

private theorem field107 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 107 = 37 := by
  have equation := assertion_of_holds holds ⟨89,by change 89 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f27,f29,f31] at equation
  linear_combination -equation

private theorem field111 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 111 = 37 := by
  have equation := assertion_of_holds holds ⟨93,by change 93 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [f22,f29] at equation
  linear_combination -equation

private theorem field115 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 115 = 20 := by
  have equation := assertion_of_holds holds ⟨97,by change 97 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [f22,f29] at equation
  linear_combination -equation

/-- All four tags are determined by the native operation equations. -/
theorem tags {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : lookupSelectors w = #v[47,37,37,20] := by
  simp only [lookupSelectors,field103 holds mode useRegister mask,
    field107 holds mode useRegister mask,field111 holds mode useRegister mask,
    field115 holds mode useRegister mask]

/-- The first dynamically pooled lookup uses the actual routed source-two limb. -/
theorem truncation_query {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 47,w 64,w 65,47] := by
  have query := NativeQueryProofs.dynamic_queries holds ⟨0,by decide⟩
  simpa only [Nat.mul_zero,Nat.add_zero,field100 holds mode useRegister mask,
    field101 holds mode useRegister mask,field102 holds mode useRegister mask,
    field103 holds mode useRegister mask] using query

/-- Original native source selection is recovered from the decoded packed mask. -/
theorem source {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    source2 w = if useRegister then #v[w 37,w 38] else #v[w 9,w 10] := by
  have selected := (NativeSelectorProofs.shift_bits holds mode useRegister mask).1
  have low := assertion_of_holds holds ⟨32,by change 32 < 117; decide⟩
  have high := assertion_of_holds holds ⟨33,by change 33 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at low high
  have first : w 47 = if useRegister then w 37 else w 9 := by
    cases useRegister
    all_goals
      simp only [Bool.false_eq_true,if_false,if_true] at selected ⊢
      rw [selected] at low
      linear_combination -low
  have second : w 48 = if useRegister then w 38 else w 10 := by
    cases useRegister
    all_goals
      simp only [Bool.false_eq_true,if_false,if_true] at selected ⊢
      rw [selected] at high
      linear_combination -high
  cases useRegister <;> simp_all [source2]


/-- Native truncation also derives the input bound and the unused zero field. -/
theorem amount {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    (source2 w)[0].val < 65536 ∧ (shiftAmount w).val = (source2 w)[0].val % 32 ∧
      (shiftAmount w).val < 32 ∧ w 65 = 0 := by
  have result := NativeFixed.truncate_shift _ (truncation_query holds mode useRegister mask) rfl
  change (w 47).val < 65536 ∧ (w 64).val = (w 47).val % 32 ∧ (w 64).val < 32 ∧ w 65 = 0
  exact ⟨result.1,result.2.1,result.2.1 ▸ Nat.mod_lt _ (by decide),result.2.2⟩

end Airbender.ReducedMachine.NativeShiftRoutingProofs
