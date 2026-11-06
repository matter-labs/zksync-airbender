import Airbender.Proofs.ReducedMachine.NativePorts
import Airbender.Proofs.ReducedMachine.NativeShiftQueries
import Airbender.Proofs.ReducedMachine.NativeShiftHeader

namespace Airbender.ReducedMachine.NativeShiftWriteProofs
open Verification Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem inactive86 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 86 = 0 := by
  have equation := assertion_of_holds holds ⟨54,by change 54 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  simp [f27] at equation
  exact equation

private theorem inactive87 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 87 = 0 := by
  have equation := assertion_of_holds holds ⟨55,by change 55 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  simp [f27] at equation
  exact equation

private theorem field116 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 116 = w 77 + w 79 := by
  have equation := assertion_of_holds holds ⟨98,by change 98 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f20 : w 20 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨0,by decide⟩
  have f21 : w 21 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨1,by decide⟩
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f26 : w 26 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨6,by decide⟩
  have f28 : w 28 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨8,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f30 : w 30 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨10,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f28,f29,f30] at equation
  have zero86 := inactive86 holds mode useRegister mask
  have zero87 := inactive87 holds mode useRegister mask
  simp [zero86,zero87] at equation
  linear_combination -equation

private theorem field117 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 117 = w 78 + w 80 := by
  have equation := assertion_of_holds holds ⟨99,by change 99 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f20 : w 20 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨0,by decide⟩
  have f21 : w 21 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨1,by decide⟩
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f26 : w 26 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨6,by decide⟩
  have f28 : w 28 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨8,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f30 : w 30 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨10,by decide⟩
  simp [f20,f21,f22,f24,f25,f26,f28,f29,f30] at equation
  have zero86 := inactive86 holds mode useRegister mask
  have zero87 := inactive87 holds mode useRegister mask
  simp [zero86,zero87] at equation
  linear_combination -equation

private theorem field118 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : w 118 = (1 - w 8) * w 116 := by
  have equation := assertion_of_holds holds ⟨100,by change 100 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  linear_combination -equation

private theorem field119 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : w 119 = (1 - w 8) * w 117 := by
  have equation := assertion_of_holds holds ⟨101,by change 101 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  linear_combination -equation

private theorem field45 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 45 = w 7 := by
  have equation := assertion_of_holds holds ⟨102,by change 102 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have update := (NativeShiftHeaderProofs.bits holds mode useRegister mask).1
  rw [update] at equation
  linear_combination -equation

private theorem field46 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 46 = 0 := by
  have equation := assertion_of_holds holds ⟨103,by change 103 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have update := (NativeShiftHeaderProofs.bits holds mode useRegister mask).1
  rw [update] at equation
  simpa using equation

private theorem field43 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 43 = w 118 := by
  have equation := assertion_of_holds holds ⟨106,by change 106 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have update := (NativeShiftHeaderProofs.bits holds mode useRegister mask).1
  rw [update] at equation
  linear_combination -equation

private theorem field44 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 44 = w 119 := by
  have equation := assertion_of_holds holds ⟨107,by change 107 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have update := (NativeShiftHeaderProofs.bits holds mode useRegister mask).1
  rw [update] at equation
  linear_combination -equation

private theorem field89 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 89 = 1 := by
  have equation := assertion_of_holds holds ⟨114,by change 114 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f31] at equation
  linear_combination -equation

private theorem field13 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 13 = w 49 := by
  have equation := assertion_of_holds holds ⟨110,by change 110 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f20 : w 20 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨0,by decide⟩
  have f21 : w 21 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨1,by decide⟩
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f26 : w 26 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨6,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f28 : w 28 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨8,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f30 : w 30 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨10,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at equation
  linear_combination -equation

private theorem field14 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 14 = w 50 := by
  have equation := assertion_of_holds holds ⟨111,by change 111 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have f20 : w 20 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨0,by decide⟩
  have f21 : w 21 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨1,by decide⟩
  have f22 : w 22 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨2,by decide⟩
  have f23 : w 23 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨3,by decide⟩
  have f24 : w 24 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨4,by decide⟩
  have f25 : w 25 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨5,by decide⟩
  have f26 : w 26 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨6,by decide⟩
  have f27 : w 27 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨7,by decide⟩
  have f28 : w 28 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨8,by decide⟩
  have f29 : w 29 = 1 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨9,by decide⟩
  have f30 : w 30 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨10,by decide⟩
  have f31 : w 31 = 0 := by simpa using (NativeSelectorProofs.shift_bits holds mode useRegister mask).2 ⟨11,by decide⟩
  simp [f20,f21,f22,f23,f24,f25,f26,f27,f28,f29,f30,f31] at equation
  linear_combination -equation

private theorem selected_low {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 77 = if mode = .left then w 66 else w 66 + w 76 := by
  have equation := assertion_of_holds holds ⟨44,by change 44 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have direction := (NativeShiftMinorProofs.bits holds mode useRegister mask).2.1
  cases mode
  all_goals
    simp at direction ⊢
    rw [direction] at equation
    linear_combination -equation

private theorem selected_high {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 78 = if mode = .left then w 75 + w 67 else w 75 := by
  have equation := assertion_of_holds holds ⟨45,by change 45 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  have direction := (NativeShiftMinorProofs.bits holds mode useRegister mask).2.1
  cases mode
  all_goals
    simp at direction ⊢
    rw [direction] at equation
    linear_combination -equation

/-- Native field assembly of actual contribution and filler fields. -/
theorem candidate {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    #v[w 116,w 117] = mode.assemble (shiftLowParts w) (shiftHighParts w) (shiftSignFill w) := by
  rw [field116 holds mode useRegister mask,field117 holds mode useRegister mask,
    selected_low holds mode useRegister mask,selected_high holds mode useRegister mask]
  cases mode <;> simp [ShiftMode.assemble,shiftLowParts,shiftHighParts,shiftSignFill]

/-- The actual native destination port receives the actual masked candidate. -/
theorem write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    rdWrite w = (mode.assemble (shiftLowParts w) (shiftHighParts w) (shiftSignFill w)).map
      (fun value => (1 - rdZeroFlag w) * value) := by
  have native : rdWrite w = (#v[w 116,w 117]).map
      (fun value => (1 - rdZeroFlag w) * value) := by
    apply Vector.ext
    intro i hi
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;>
      simp [rdWrite,rdPort,importedConstraintsMemoryPorts,Trace.WordColumns.evaluate,
        rdZeroFlag,importedConstraintsDecoderColumns,
        field43 holds mode useRegister mask,field44 holds mode useRegister mask,
        field118 holds,field119 holds]
  rw [candidate holds mode useRegister mask] at native
  exact native

/-- Native mixed-port metadata and equations select the imported rd field. -/
theorem address {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) := by
  rw [NativePortProofs.address_columns]
  simp [Trace.MemoryAddress.code,Trace.pairCode,field89 holds mode useRegister mask,
    field45 holds mode useRegister mask,field46 holds mode useRegister mask,rdIndex,
    importedConstraintsDecoderColumns]

/-- Select the actual default PC candidate; numerical successor meaning is separate. -/
theorem pc {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : finalPC w = defaultPC w := by
  unfold finalPC
  rw [NativePortProofs.final_pc_columns]
  apply Vector.ext
  intro i hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> simp [defaultPC,field13 holds mode useRegister mask,
    field14 holds mode useRegister mask]

end Airbender.ReducedMachine.NativeShiftWriteProofs
