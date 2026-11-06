import Airbender.Proofs.ReducedMachine.NativeShiftFill

namespace Airbender.ReducedMachine.Native
open Verification

/-- Native sign/high-byte facts, derived from the regenerated constraints and
    complete fixed pool for the explicitly retained public setup fixture. -/
theorem sign_high_queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (importedConstraints NativeFixed.table)) :
    (w 36).val < 65536 ∧ (w 56).val = (w 36).val / 32768 ∧
      (w 57).val = (w 36).val / 256 ∧
    (w 48).val < 65536 ∧ (w 59).val = (w 48).val / 32768 ∧
      (w 60).val = (w 48).val / 256 :=
  NativeQueryProofs.results holds

/-- Every dynamic query selector is derived to belong to the actual native pool. -/
theorem lookup_selectors {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (importedConstraints NativeFixed.table)) (slot : Fin 4) :
    (w (103 + 4 * slot.val)).val ∈ NativeFixed.tags :=
  NativeQueryProofs.dynamic_selectors holds slot

/-- Under the explicit decoded shift mask, native acceptance determines the
    actual source route, all lookup tags and the bounded five-bit shift amount. -/
theorem shift_routing {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    source2 w = (if useRegister then #v[w 37,w 38] else #v[w 9,w 10]) ∧
      lookupSelectors w = #v[47,37,37,20] ∧
      (source2 w)[0].val < 65536 ∧ (shiftAmount w).val = (source2 w)[0].val % 32 ∧
      (shiftAmount w).val < 32 ∧ w 65 = 0 :=
  ⟨NativeShiftRoutingProofs.source holds mode useRegister mask,
    NativeShiftRoutingProofs.tags holds mode useRegister mask,
    NativeShiftRoutingProofs.amount holds mode useRegister mask⟩

/-- The actual native filler is derived from the input sign, mode and truncated
    amount, retaining logical/positive-input/zero-shift cases. -/
theorem shift_sign_fill {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    (shiftSignFill w)[0].val + 65536 * (shiftSignFill w)[1].val =
      mode.filler (w 36).val (shiftAmount w).val ∧
      (shiftSignFill w)[0].val < 65536 ∧ (shiftSignFill w)[1].val < 65536 :=
  NativeShiftFillProofs.result holds mode useRegister mask

end Airbender.ReducedMachine.Native
