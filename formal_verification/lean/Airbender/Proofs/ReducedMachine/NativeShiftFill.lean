import Airbender.Proofs.ReducedMachine.NativeShiftRouting
import Airbender.Proofs.ReducedMachine.NativeShiftMinor
import Airbender.Proofs.ReducedMachine.SignFillReference

namespace Airbender.ReducedMachine.NativeShiftFillProofs
open Verification Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem field112 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 112 = 2 * w 32 + w 56 + 4 * w 64 := by
  have equation := assertion_of_holds holds ⟨94,by change 94 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have binary : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have shift : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [binary,shift] at equation
  linear_combination -equation

private theorem field113 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 113 = w 79 := by
  have equation := assertion_of_holds holds ⟨95,by change 95 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have binary : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have shift : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [binary,shift] at equation
  linear_combination -equation

private theorem field114 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 114 = w 80 := by
  have equation := assertion_of_holds holds ⟨96,by change 96 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have binary : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have shift : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  simp [binary,shift] at equation
  linear_combination -equation

/-- Actual fourth pooled query, with no supplied selector or query payload. -/
theorem query {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[2 * w 32 + w 56 + 4 * w 64,w 79,w 80,20] := by
  have member := NativeQueryProofs.dynamic_queries holds ⟨3,by decide⟩
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 112,w 113,w 114,w 115] at member
  have tags := NativeShiftRoutingProofs.tags holds mode useRegister mask
  have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) tags
  change w 115 = 20 at tag
  simpa only [field112 holds mode useRegister mask,field113 holds mode useRegister mask,
    field114 holds mode useRegister mask,tag] using member

/-- Bounds, sign and amount are recovered from accepted native queries. -/
theorem result {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    (shiftSignFill w)[0].val + 65536 * (shiftSignFill w)[1].val =
      mode.filler (w 36).val (shiftAmount w).val ∧
      (shiftSignFill w)[0].val < 65536 ∧ (shiftSignFill w)[1].val < 65536 := by
  have native := NativeFixed.sign_fill _ (query holds mode useRegister mask) rfl
  simp only [Vector.getElem_mk,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ] at native
  have sign := NativeQueryProofs.results holds
  have amount := NativeShiftRoutingProofs.amount holds mode useRegister mask
  have minor := (NativeShiftMinorProofs.bits holds mode useRegister mask).1
  let flag : Nat := if mode = .arithmetic then 1 else 0
  have flagBound : flag ≤ 1 := by dsimp [flag]; split <;> omega
  have flagField : (flag : ZMod mersenne31Modulus) = w 32 := by
    cases mode <;> simpa [flag] using minor.symm
  let key := 2 * flag + (w 56).val + 4 * (w 64).val
  have signBound : (w 56).val ≤ 1 := by have bound := sign.1; have same := sign.2.1; omega
  have keyBound : key < 128 := by dsimp [key]; have bound := amount.2.2.1; change (w 64).val < 32 at bound; omega
  have field : (key : ZMod mersenne31Modulus) = 2 * w 32 + w 56 + 4 * w 64 := by
    simp only [key,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val,flagField]
  have canonical : (2 * w 32 + w 56 + 4 * w 64).val = key := by
    rw [← field,ZMod.val_natCast_of_lt (by change key < 2147483647; omega)]
  have low := native.2.1
  have high := native.2.2.1
  simp only [canonical] at low high
  have reference : NativeFixed.signFillMask key = mode.filler (w 36).val (w 64).val := by
    dsimp [key,flag]
    rw [sign.2.1]
    exact SignFillReferenceProofs.reference mode _ _ sign.1
  change (w 79).val + 65536 * (w 80).val = mode.filler (w 36).val (w 64).val ∧
    (w 79).val < 65536 ∧ (w 80).val < 65536
  refine ⟨?_,native.2.2.2⟩
  rw [low,high]
  simp only [NativeFixed.signFillOutputs,Vector.getElem_mk,List.getElem_toArray,
    List.getElem_cons_zero,List.getElem_cons_succ]
  rw [Nat.mod_add_div,reference]

end Airbender.ReducedMachine.NativeShiftFillProofs
