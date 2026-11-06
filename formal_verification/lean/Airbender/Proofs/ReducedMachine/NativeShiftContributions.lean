import Airbender.Review.Circuits.ReducedMachine.ShiftContributions
import Airbender.Review.Circuits.ReducedMachine.Tables.ShiftTheorems
import Airbender.Proofs.ReducedMachine.NativeShiftQueries

namespace Airbender.ReducedMachine.NativeShiftContributionProofs
open Verification Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem fields (key : ZMod mersenne31Modulus)
    (parts : Vector (ZMod mersenne31Modulus) 2)
    (member : (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[key,parts[0],parts[1],37]) :
    key.val < 4194304 ∧ parts[0].val = (NativeFixed.shiftOutputs key.val)[0] ∧
      parts[1].val = (NativeFixed.shiftOutputs key.val)[1] ∧
      parts[0].val < 65536 ∧ parts[1].val < 65536 :=
  NativeFixed.shift_implementation _ member rfl

/-- Actual accepted query fields; canonical source-key decoding remains a separate obligation. -/
theorem values {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) (limb : Fin 2) :
    (mode.lookupKey (source1 w)[limb] (shiftAmount w)).val < 4194304 ∧
      (shiftContribution w limb)[0].val =
        (NativeFixed.shiftOutputs (mode.lookupKey (source1 w)[limb] (shiftAmount w)).val)[0] ∧
      (shiftContribution w limb)[1].val =
        (NativeFixed.shiftOutputs (mode.lookupKey (source1 w)[limb] (shiftAmount w)).val)[1] ∧
      (shiftContribution w limb)[0].val < 65536 ∧ (shiftContribution w limb)[1].val < 65536 := by
  have queries := NativeShiftQueryProofs.queries holds mode useRegister mask
  fin_cases limb
  · exact fields _ _ queries.1
  · exact fields _ _ queries.2

end Airbender.ReducedMachine.NativeShiftContributionProofs
