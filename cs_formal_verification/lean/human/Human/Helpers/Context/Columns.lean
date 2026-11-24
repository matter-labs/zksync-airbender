module
public import Human.Helpers.Context.Timestamps

@[expose] public section

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

end Airbender.Trace
