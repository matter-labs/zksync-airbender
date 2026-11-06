import Airbender.Review.Circuits.ReducedMachine.Theorems

namespace Tests.NativeReducedShift
open Airbender Airbender.ReducedMachine Airbender.Verification

/-- The actual native truncation region cannot accept a seventeenth input bit. -/
theorem oversized_key_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[65536,0,0,47] := by
  intro member
  have bound := (NativeFixed.truncate_shift _ member rfl).1
  exact (by decide +kernel : ¬ (65536 : ZMod mersenne31Modulus).val < 65536) bound

theorem wrong_remainder_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[65535,30,0,47] := by
  intro member
  have result := (NativeFixed.truncate_shift _ member rfl).2.1
  exact (by decide +kernel : ¬ (30 : ZMod mersenne31Modulus).val =
    (65535 : ZMod mersenne31Modulus).val % 32) result

theorem nonzero_unused_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[65535,31,1,47] := by
  intro member
  have result := (NativeFixed.truncate_shift _ member rfl).2.2
  exact (by decide +kernel : (1 : ZMod mersenne31Modulus) ≠ 0) result

/-- Immediate routing reaches truncation before any initialized-history premise. -/
theorem immediate_last_limb {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (mode : Native.ShiftMode) (mask : w 12 = (mode.mask false : ZMod mersenne31Modulus))
    (immediate : (w 9).val = 65535) : (Native.shiftAmount w).val = 31 := by
  have route := NativeShiftRoutingProofs.source holds mode false mask
  have value := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) route
  change w 47 = w 9 at value
  have amount := (NativeShiftRoutingProofs.amount holds mode false mask).2.1
  change (Native.shiftAmount w).val = (w 47).val % 32 at amount
  rw [value,immediate] at amount
  exact amount

/-- Register routing uses the register port, including the zero-shift boundary. -/
theorem register_zero_limb {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (mode : Native.ShiftMode) (mask : w 12 = (mode.mask true : ZMod mersenne31Modulus))
    (register : (w 37).val = 0) : (Native.shiftAmount w).val = 0 := by
  have route := NativeShiftRoutingProofs.source holds mode true mask
  have value := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) route
  change w 47 = w 37 at value
  have amount := (NativeShiftRoutingProofs.amount holds mode true mask).2.1
  change (Native.shiftAmount w).val = (w 47).val % 32 at amount
  rw [value,register] at amount
  exact amount

/-- The standalone sign-fill selector 52 cannot replace this machine's ID 20. -/
theorem standalone_selector_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) : w 115 ≠ 52 := by
  have tags := NativeShiftRoutingProofs.tags holds mode useRegister mask
  have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) tags
  change w 115 = 20 at selected
  rw [selected]
  decide +kernel

end Tests.NativeReducedShift
