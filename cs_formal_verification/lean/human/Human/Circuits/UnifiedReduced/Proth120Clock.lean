module
public import Human.Circuits.UnifiedReduced.Proth120Artifact
public import Human.Helpers.Properties

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Verification

abbrev clockConstraints (setup : Table (ZMod proth120Modulus) (fields 10)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

/-- The two checked clock limbs advance by four, including a carry across the 19-bit boundary. -/
def ClockAdvanceClaim : Prop :=
  ∀ setup (w : Nat → ZMod proth120Modulus),
    FlatOperation.ConstraintsHoldFlat (environment w) (clockConstraints setup) →
    (decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded →
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).value =
      (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 4

def ClockAdvanceSatisfiableClaim : Prop :=
  ∃ (setup : Table (ZMod proth120Modulus) (fields 10)) (w : Nat → ZMod proth120Modulus),
    FlatOperation.ConstraintsHoldFlat (environment w) (clockConstraints setup) ∧
    (decodeTimestamp w importedConstraintsTraceColumns.initialTime).Bounded ∧ w 4 = 1

end Airbender.UnifiedReduced.Proth120
