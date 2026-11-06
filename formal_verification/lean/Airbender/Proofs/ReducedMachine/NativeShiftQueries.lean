import Airbender.Review.Circuits.ReducedMachine.ShiftWrite
import Airbender.Proofs.ReducedMachine.NativeShiftMinor
import Airbender.Proofs.ReducedMachine.NativeShiftRouting

namespace Airbender.ReducedMachine.NativeShiftQueryProofs
open Verification Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem field104 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 104 = 2097152 * w 33 + 65536 * w 64 + w 35 := by
  have equation := assertion_of_holds holds ⟨86,by change 86 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f27,f29,f31] at equation
  linear_combination -equation

private theorem field105 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 105 = w 66 := by
  have equation := assertion_of_holds holds ⟨87,by change 87 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f27,f29,f31] at equation
  linear_combination -equation

private theorem field106 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 106 = w 67 := by
  have equation := assertion_of_holds holds ⟨88,by change 88 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f22,f23,f27,f29,f31] at equation
  linear_combination -equation

private theorem field108 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 108 = 2097152 * w 33 + 65536 * w 64 + w 36 := by
  have equation := assertion_of_holds holds ⟨90,by change 90 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [f22,f29] at equation
  linear_combination -equation

private theorem field109 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 109 = w 75 := by
  have equation := assertion_of_holds holds ⟨91,by change 91 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [f22,f29] at equation
  linear_combination -equation

private theorem field110 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 110 = w 76 := by
  have equation := assertion_of_holds holds ⟨92,by change 92 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [f22,f29] at equation
  linear_combination -equation

/-- Exact accepted contribution queries; their arithmetic meaning remains separate. -/
theorem queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[mode.lookupKey (source1 w)[0] (shiftAmount w),(shiftLowParts w)[0],(shiftLowParts w)[1],37] ∧
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[mode.lookupKey (source1 w)[1] (shiftAmount w),(shiftHighParts w)[0],(shiftHighParts w)[1],37] := by
  have low := NativeQueryProofs.dynamic_queries holds ⟨1,by decide⟩
  have high := NativeQueryProofs.dynamic_queries holds ⟨2,by decide⟩
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 104,w 105,w 106,w 107] at low
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 108,w 109,w 110,w 111] at high
  have tags := NativeShiftRoutingProofs.tags holds mode useRegister mask
  have lowTag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[1]) tags
  have highTag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[2]) tags
  change w 107 = 37 at lowTag
  change w 111 = 37 at highTag
  rw [field104 holds mode useRegister mask,field105 holds mode useRegister mask,field106 holds mode useRegister mask,lowTag] at low
  rw [field108 holds mode useRegister mask,field109 holds mode useRegister mask,field110 holds mode useRegister mask,highTag] at high
  have direction := (NativeShiftMinorProofs.bits holds mode useRegister mask).2.1
  have keyLow : 2097152 * w 33 + 65536 * w 64 + w 35 = mode.lookupKey (source1 w)[0] (shiftAmount w) := by
    change _ = w 35 + 65536 * w 64 + 2097152 * (if mode = .left then 0 else 1)
    rw [direction]
    ring
  have keyHigh : 2097152 * w 33 + 65536 * w 64 + w 36 = mode.lookupKey (source1 w)[1] (shiftAmount w) := by
    change _ = w 36 + 65536 * w 64 + 2097152 * (if mode = .left then 0 else 1)
    rw [direction]
    ring
  simp only [Nat.cast_ofNat] at keyLow keyHigh
  constructor
  · rw [keyLow] at low
    exact low
  · rw [keyHigh] at high
    exact high

end Airbender.ReducedMachine.NativeShiftQueryProofs
