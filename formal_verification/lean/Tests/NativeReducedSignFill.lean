import Airbender.Review.Circuits.ReducedMachine.Theorems

namespace Tests.NativeReducedSignFill
open Airbender Airbender.ReducedMachine Airbender.Verification

theorem negative_zero_shift :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[3,0,0,20] := by
  refine ⟨⟨393220,by decide⟩,?_⟩
  decide +kernel

theorem negative_shift16 :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[67,0,65535,20] := by
  refine ⟨⟨393284,by decide⟩,?_⟩
  decide +kernel

theorem negative_shift17 :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[71,32768,65535,20] := by
  refine ⟨⟨393288,by decide⟩,?_⟩
  decide +kernel

theorem negative_shift31 :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[127,65534,65535,20] := by
  refine ⟨⟨393344,by decide⟩,?_⟩
  decide +kernel

theorem logical_negative_shift31 :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[125,0,0,20] := by
  refine ⟨⟨393342,by decide⟩,?_⟩
  decide +kernel

theorem positive_arithmetic_shift31 :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[126,0,0,20] := by
  refine ⟨⟨393343,by decide⟩,?_⟩
  decide +kernel

theorem incorrect_last_bit_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[127,65535,65535,20] := by
  intro member
  have result := (NativeFixed.sign_fill _ member rfl).2.1
  exact (by decide +kernel : ¬ (65535 : ZMod mersenne31Modulus).val =
    (NativeFixed.signFillOutputs (127 : ZMod mersenne31Modulus).val)[0]) result

theorem zero_shift_nonzero_fill_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[3,0,65535,20] := by
  intro member
  have result := (NativeFixed.sign_fill _ member rfl).2.2.1
  exact (by decide +kernel : ¬ (65535 : ZMod mersenne31Modulus).val =
    (NativeFixed.signFillOutputs (3 : ZMod mersenne31Modulus).val)[1]) result

/-- The zero-shift exception is retained by actual selected-row constraints. -/
theorem arithmetic_zero_amount {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (useRegister : Bool)
    (mask : w 12 = (Native.ShiftMode.arithmetic.mask useRegister : ZMod mersenne31Modulus))
    (amount : (w 64).val = 0) :
    (Native.shiftSignFill w)[0].val + 65536 * (Native.shiftSignFill w)[1].val = 0 := by
  have result := (Native.shift_sign_fill holds .arithmetic useRegister mask).1
  simpa [Native.ShiftMode.filler,Native.shiftAmount,amount] using result

/-- Logical right shift cannot pick up arithmetic filler from a negative input. -/
theorem logical_right_no_fill {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (useRegister : Bool)
    (mask : w 12 = (Native.ShiftMode.right.mask useRegister : ZMod mersenne31Modulus)) :
    (Native.shiftSignFill w)[0].val + 65536 * (Native.shiftSignFill w)[1].val = 0 := by
  simpa [Native.ShiftMode.filler] using (Native.shift_sign_fill holds .right useRegister mask).1

/-- At shift31 the low filler's final bit stays clear, on actual native rows. -/
theorem arithmetic_negative_last {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (useRegister : Bool)
    (mask : w 12 = (Native.ShiftMode.arithmetic.mask useRegister : ZMod mersenne31Modulus))
    (negative : 32768 ≤ (w 36).val) (amount : (w 64).val = 31) :
    (Native.shiftSignFill w)[0].val + 65536 * (Native.shiftSignFill w)[1].val = 4294967294 := by
  have result := (Native.shift_sign_fill holds .arithmetic useRegister mask).1
  simpa [Native.ShiftMode.filler,Native.shiftAmount,negative,amount] using result

end Tests.NativeReducedSignFill
