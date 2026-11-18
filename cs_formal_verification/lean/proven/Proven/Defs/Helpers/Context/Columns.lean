module
public import Human.Helpers.Context.Timestamps
public import Human.Helpers.Context.Columns

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Context/Columns.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Trace
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
