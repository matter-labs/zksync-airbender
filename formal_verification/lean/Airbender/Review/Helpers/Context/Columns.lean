import Airbender.Review.Helpers.Context.Timestamps

namespace Airbender.Trace

/-- Imported clock columns for one actual memory access, including the compiler's
    Boolean comparison borrow and its in-cycle write offset. -/
structure TimestampPort where
  /-- This port's in-cycle write time relative to the row's starting clock. -/
  offset : Nat
  /-- Variable IDs for the timestamp of the value read by this port. -/
  previous : Vector Nat 2
  /-- Variable ID for the Boolean borrow used in the strict-time comparison. -/
  borrow : Nat
  deriving DecidableEq

/-- Placement-resolved machine-state and memory timestamp metadata from JSON.
    These names interpret native columns; they supply no semantic conclusion. -/
structure TraceColumns where
  /-- Variable ID of the active-row flag. -/
  execute : Nat
  /-- Variable IDs for the two initial PC limbs. -/
  initialPC : Vector Nat 2
  /-- Variable IDs for the two final PC limbs. -/
  finalPC : Vector Nat 2
  /-- Variable IDs for the two initial machine-clock limbs. -/
  initialTime : Vector Nat 2
  /-- Variable IDs for the two final machine-clock limbs. -/
  finalTime : Vector Nat 2
  /-- Imported clock descriptors for this family's memory ports. -/
  ports : Array TimestampPort
  deriving DecidableEq

/-- Inputs needed by a local clock calculation for assignment `w`. Imported
    column IDs select the current clock and previous port timestamps. Integrated
    trace proofs derive these conditions from public clock boundaries and
    matching, so they are not caller-supplied per-row assumptions. -/
structure ClockInputs {p : Nat} (columns : TraceColumns) (w : Nat → ZMod p) : Prop where
  initial : (decodeTimestamp w columns.initialTime).Bounded
  aligned : (decodeTimestamp w columns.initialTime).lo % 4 = 0
  previous : ∀ port ∈ columns.ports, (decodeTimestamp w port.previous).Bounded

/-- Clock facts proved for one row: the machine clock advances by four
    without wrapping, and each port occurs after its previous write and before
    the next machine clock. Port offsets come from imported metadata. -/
structure ClockEffects {p : Nat} (columns : TraceColumns) (w : Nat → ZMod p) : Prop where
  finalBound : (decodeTimestamp w columns.finalTime).Bounded
  advances : (decodeTimestamp w columns.finalTime).value =
    (decodeTimestamp w columns.initialTime).value + 4
  accesses : ∀ port ∈ columns.ports,
    (decodeTimestamp w port.previous).value <
      (decodeTimestamp w columns.initialTime).value + port.offset ∧
    (decodeTimestamp w columns.initialTime).value + port.offset <
      (decodeTimestamp w columns.finalTime).value

end Airbender.Trace
