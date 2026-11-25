module
public import Proven.UnifiedReduced.Standard.Clocks

@[expose] public section
namespace Airbender.UnifiedReduced.Proofs
open Trace
set_option maxRecDepth 8192

private theorem babyBear_coefficient {p : Nat} : (Standard.Profile.babyBear.clockInv : ZMod p) = -3840 := by
  change ((-(3840 : Int) : Int) : ZMod p) = -3840
  norm_num

private theorem babyBear_inverse {p : Nat} (h : (-3840 : ZMod p) * 524288 = 1) :
    Standard.Profile.babyBear.clockInv * 524288 = (1 : ZMod p) := by rwa [babyBear_coefficient]

private theorem babyBear_square {p : Nat} :
    (Standard.Profile.babyBear.clockInv : ZMod p) * Standard.Profile.babyBear.clockInv =
      Standard.Profile.babyBear.clockSquare := by
  rw [babyBear_coefficient]
  change (-3840 : ZMod p) * -3840 = ((14745600 : Int) : ZMod p)
  norm_num

theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∃ carry : Nat, carry ≤ 1 ∧ w 2 + 4 = w 32 + 524288 * carry ∧ w 3 + carry = w 33 := by
  exact Standard.clock_equations (profile := .babyBear) (babyBear_inverse inverse) babyBear_square h

theorem final_clock_bound {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup)) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded := by
  exact Standard.final_clock_bound (Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups))

theorem clock_advance {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (initial : (decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).value =
      (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 4 := by
  exact Standard.clock_advance (profile := .babyBear) hp (babyBear_inverse inverse) babyBear_square
    (Verification.holds_of_sublist h (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups))
    (Verification.holds_of_sublist h (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)) initial

theorem clocks {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (inputs : ClockInputs importedConstraintsTraceColumns w) :
    ClockEffects importedConstraintsTraceColumns w := by
  exact Standard.clock_accesses (profile := .babyBear) hp (babyBear_inverse inverse) babyBear_square
    (Verification.holds_of_sublist h (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups))
    (Verification.holds_of_sublist h (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)) inputs

end Airbender.UnifiedReduced.Proofs
