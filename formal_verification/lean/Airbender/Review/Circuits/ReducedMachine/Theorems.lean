import Airbender.Proofs.ReducedMachine.NativeShiftFill
import Airbender.Proofs.ReducedMachine.NativeShiftWrite
import Airbender.Proofs.ReducedMachine.NativeShiftContributions

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

/-- Actual table-37 inputs and contribution fields; arithmetic table meaning is separate. -/
theorem shift_table_queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[mode.lookupKey (source1 w)[0] (shiftAmount w),(shiftLowParts w)[0],(shiftLowParts w)[1],37] ∧
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[mode.lookupKey (source1 w)[1] (shiftAmount w),(shiftHighParts w)[0],(shiftHighParts w)[1],37] :=
  NativeShiftQueryProofs.queries holds mode useRegister mask

/-- Native acceptance fixes both bounded numerical contributions at the actual packed key.
    This does not yet identify that field key with an initialized architectural source word. -/
theorem shift_contribution_values {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) (limb : Fin 2) :
    (mode.lookupKey (source1 w)[limb] (shiftAmount w)).val < 4194304 ∧
      (shiftContribution w limb)[0].val =
        (NativeFixed.shiftOutputs (mode.lookupKey (source1 w)[limb] (shiftAmount w)).val)[0] ∧
      (shiftContribution w limb)[1].val =
        (NativeFixed.shiftOutputs (mode.lookupKey (source1 w)[limb] (shiftAmount w)).val)[1] ∧
      (shiftContribution w limb)[0].val < 65536 ∧ (shiftContribution w limb)[1].val < 65536 :=
  NativeShiftContributionProofs.values holds mode useRegister mask limb

/-- Native destination selection and actual masked contribution assembly. -/
theorem shift_masked_write {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
    rdWrite w = (mode.assemble (shiftLowParts w) (shiftHighParts w) (shiftSignFill w)).map
      (fun value => (1 - rdZeroFlag w) * value) :=
  ⟨NativeShiftWriteProofs.address holds mode useRegister mask,
    NativeShiftWriteProofs.write holds mode useRegister mask⟩

/-- Select the actual default-PC candidate; numerical successor meaning is separate. -/
theorem shift_default_pc {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) :
    finalPC w = defaultPC w :=
  NativeShiftWriteProofs.pc holds mode useRegister mask

end Airbender.ReducedMachine.Native
