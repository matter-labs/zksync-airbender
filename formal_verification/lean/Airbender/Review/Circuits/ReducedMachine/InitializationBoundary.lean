import Airbender.Review.Circuits.ReducedMachine.InitializationSorted

namespace Airbender.NativeInitializationBoundary
open Airbender.NativeInitializationOrdering Airbender.ReducedMachine.Native

/-- Actual native address, teardown value and teardown timestamp, in the helper's
    order. These are RAW field limbs; no value/timestamp codec or bounds assumed. -/
def record (w : Nat → F) : Vector F 6 :=
  #v[(address w)[0],(address w)[1],
    w importedConstraintsArgumentColumns.terminalValue[0],w importedConstraintsArgumentColumns.terminalValue[1],
    w importedConstraintsArgumentColumns.terminalTime[0],w importedConstraintsArgumentColumns.terminalTime[1]]

/-- Observed native public auxiliary-boundary values, NOT prescribed seeds or
    a desired first/last address. Rust/u32/field/transcript refinement is separate. -/
structure PublicValues where
  first : Vector F 6
  oneBeforeLast : Vector F 6

def addressValue (values : Vector F 6) : Nat := values[0].val+65536*values[1].val

/-- Actual source boundary polynomial: only the trace value receives tau.
    The public constant is unscaled. -/
def term {R : Type} [CommRing R] (tau actual values : R) : R := tau*actual-values

/-- Individual unit-normalized source relations, distinct from physical quotient
    extraction. All six actual fields are bound; none may be silently dropped. -/
def EndpointAccepted (w : Nat → F) (values : Vector F 6) : Prop :=
  ∀ slot : Fin 6, term 1 (record w)[slot.val] values[slot.val] = 0

/-- SAME complete scalar/main/init/sorting input and actual twelve native public
    boundary relations. No window/order/image/seed/expected first-last premise.
    Last ordinary row is N-2; reserved normalized N-1 is NOT this public endpoint. -/
structure Accepted {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    (proof : Airbender.NativeScalar16Arguments.Proof R) (values : PublicValues) : Prop where
  scalar : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof
  first : EndpointAccepted (proof.initialization.main.rows 0) values.first
  oneBeforeLast : EndpointAccepted (proof.initialization.main.rows (scalar16Layout.traceLength-2)) values.oneBeforeLast

end Airbender.NativeInitializationBoundary
