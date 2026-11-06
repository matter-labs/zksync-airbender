import Airbender.Review.Circuits.ReducedMachine.Theorems

namespace Tests.NativeReducedWrite
open Airbender Airbender.ReducedMachine Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The actual port discards the candidate for every shift mode. This does not
    assume that the public decoder has bound the zero flag to architectural rd. -/
theorem discarded_write {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (discarded : Native.rdZeroFlag w = 1) : Native.rdWrite w = #v[0,0] := by
  have result := (Native.shift_masked_write holds mode useRegister mask).2
  cases mode <;> simpa [Native.ShiftMode.assemble,discarded] using result

/-- A masked nonzero actual write cannot satisfy the original native constraints. -/
theorem discarded_nonzero_rejected {w : Nat → ZMod mersenne31Modulus}
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (discarded : Native.rdZeroFlag w = 1) (nonzero : Native.rdWrite w ≠ #v[0,0]) :
    ¬ FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table) := by
  intro holds
  exact nonzero (discarded_write holds mode useRegister mask discarded)

private theorem logical_fill_zero {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (logical : mode = .left ∨ mode = .right) : w 79 = 0 ∧ w 80 = 0 := by
  have result := (Native.shift_sign_fill holds mode useRegister mask).1
  rcases logical with rfl | rfl
  all_goals
    have zero : (w 79).val + 65536 * (w 80).val = 0 := by
      simpa [Native.ShiftMode.filler,Native.shiftSignFill] using result
    constructor
    · apply ZMod.val_injective mersenne31Modulus
      change (w 79).val = 0
      omega
    · apply ZMod.val_injective mersenne31Modulus
      change (w 80).val = 0
      omega

/-- Native right-shift cross-limb contribution enters the low destination limb. -/
theorem logical_right_assembly {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (useRegister : Bool)
    (mask : w 12 = (Native.ShiftMode.right.mask useRegister : ZMod mersenne31Modulus))
    (unmasked : Native.rdZeroFlag w = 0) : Native.rdWrite w = #v[w 66 + w 76,w 75] := by
  have fill := logical_fill_zero holds .right useRegister mask (Or.inr rfl)
  simpa [Native.ShiftMode.assemble,Native.shiftLowParts,Native.shiftHighParts,
    Native.shiftSignFill,unmasked,fill.1,fill.2] using
    (Native.shift_masked_write holds .right useRegister mask).2

/-- Native left-shift cross-limb contribution enters the high destination limb. -/
theorem logical_left_assembly {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (useRegister : Bool)
    (mask : w 12 = (Native.ShiftMode.left.mask useRegister : ZMod mersenne31Modulus))
    (unmasked : Native.rdZeroFlag w = 0) : Native.rdWrite w = #v[w 66,w 75 + w 67] := by
  have fill := logical_fill_zero holds .left useRegister mask (Or.inl rfl)
  simpa [Native.ShiftMode.assemble,Native.shiftLowParts,Native.shiftHighParts,
    Native.shiftSignFill,unmasked,fill.1,fill.2] using
    (Native.shift_masked_write holds .left useRegister mask).2

/-- Zero shift suppresses arithmetic fill even for a negative source. -/
theorem arithmetic_zero_assembly {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (useRegister : Bool)
    (mask : w 12 = (Native.ShiftMode.arithmetic.mask useRegister : ZMod mersenne31Modulus))
    (unmasked : Native.rdZeroFlag w = 0) (amount : (w 64).val = 0) :
    Native.rdWrite w = #v[w 66 + w 76,w 75] := by
  have result := (Native.shift_sign_fill holds .arithmetic useRegister mask).1
  have zero : (w 79).val + 65536 * (w 80).val = 0 := by
    simpa [Native.ShiftMode.filler,Native.shiftSignFill,Native.shiftAmount,amount] using result
  have low : w 79 = 0 := by
    apply ZMod.val_injective mersenne31Modulus
    change (w 79).val = 0
    omega
  have high : w 80 = 0 := by
    apply ZMod.val_injective mersenne31Modulus
    change (w 80).val = 0
    omega
  simpa [Native.ShiftMode.assemble,Native.shiftLowParts,Native.shiftHighParts,
    Native.shiftSignFill,unmasked,low,high] using
    (Native.shift_masked_write holds .arithmetic useRegister mask).2

/-- Discarding the write retains both actual selected queries and their contributions. -/
theorem discarded_queries_retained {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (discarded : Native.rdZeroFlag w = 1) : Native.rdWrite w = #v[0,0] ∧
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[mode.lookupKey (Native.source1 w)[0] (Native.shiftAmount w),
        (Native.shiftLowParts w)[0],(Native.shiftLowParts w)[1],37] ∧
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[mode.lookupKey (Native.source1 w)[1] (Native.shiftAmount w),
        (Native.shiftHighParts w)[0],(Native.shiftHighParts w)[1],37] :=
  ⟨discarded_write holds mode useRegister mask discarded,
    Native.shift_table_queries holds mode useRegister mask⟩

/-- Mismatching either final-PC limb fails native acceptance, without a PC+4 premise. -/
theorem pc_low_mismatch_rejected {w : Nat → ZMod mersenne31Modulus}
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) (wrong : w 13 ≠ w 49) :
    ¬ FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table) := by
  intro holds
  have result := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0])
    (Native.shift_default_pc holds mode useRegister mask)
  exact wrong (by simpa [Native.finalPC,Native.defaultPC,Native.importedConstraintsTraceColumns] using result)

theorem pc_high_mismatch_rejected {w : Nat → ZMod mersenne31Modulus}
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) (wrong : w 14 ≠ w 50) :
    ¬ FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table) := by
  intro holds
  have result := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1])
    (Native.shift_default_pc holds mode useRegister mask)
  exact wrong (by simpa [Native.finalPC,Native.defaultPC,Native.importedConstraintsTraceColumns] using result)

end Tests.NativeReducedWrite
