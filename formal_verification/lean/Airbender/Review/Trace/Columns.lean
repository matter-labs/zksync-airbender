import Airbender.Review.Trace.Timestamps

namespace Airbender.Trace

/-- Imported clock columns for one actual memory access, including the compiler's
    Boolean comparison borrow and its in-cycle write offset. -/
structure TimestampPort where
  offset : Nat
  previous : Vector Nat 2
  borrow : Nat
  deriving DecidableEq

/-- Placement-resolved machine-state and memory timestamp metadata from JSON.
    These names interpret native columns; they supply no semantic conclusion. -/
structure TraceColumns where
  execute : Nat
  initialPC : Vector Nat 2
  finalPC : Vector Nat 2
  initialTime : Vector Nat 2
  finalTime : Vector Nat 2
  ports : Array TimestampPort
  deriving DecidableEq

/-- Bounds inherited from the state and memory histories. They are still open
    interfaces until those histories are bound to the imported rows. -/
structure ClockInputs {p : Nat} (columns : TraceColumns) (w : Nat → ZMod p) : Prop where
  initial : (decodeTimestamp w columns.initialTime).Bounded
  aligned : (decodeTimestamp w columns.initialTime).lo % 4 = 0
  previous : ∀ port ∈ columns.ports, (decodeTimestamp w port.previous).Bounded

/-- The next clock advances without wrapping. Every port is strictly later than
    its previous write and lies before the next row's clock. Offsets are imported. -/
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
