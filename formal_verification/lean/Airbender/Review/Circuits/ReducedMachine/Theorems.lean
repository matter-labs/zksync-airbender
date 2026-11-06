import Airbender.Proofs.ReducedMachine.NativeQueries

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

end Airbender.ReducedMachine.Native
