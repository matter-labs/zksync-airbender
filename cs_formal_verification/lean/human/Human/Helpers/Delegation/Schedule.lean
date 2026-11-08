module
public import Human.Helpers.Context.Registries.Pooled
public import Human.Helpers.Delegation.Decoder
public import Human.Helpers.Delegation.WorkerContext

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace
variable {Kind : Type} [CircuitLayout Kind]

/-- The machine's imported starting clock, interpreted as a natural number.
    The shared state path proves its limbs are canonical. -/
abbrev startClock (row : Trace.Row p Kind) : Nat := row.clock

/-- The same row's imported ending clock. Native equations advance it by four. -/
def finishClock (row : Trace.Row p Kind) : Nat :=
  (decodeTimestamp row.assignment row.columns.finalTime).value

/-- Where one issued worker falls inside its caller's native cycle.
    These are conclusions from clock equations and request matching. Worker
    reads can refer to older writes; `writes` describes the new write clock.
    Clean access times add one to native clocks to reserve time zero for seeds. -/
structure WorkerSlot (caller : Trace.Row p Kind) (worker : Delegation.Row p) : Prop where
  /-- The actual invocation occurs one tick after the caller starts. -/
  invocation : (decodeTimestamp worker.assignment worker.columns.invocation).value = startClock caller + 1
  /-- Every native worker port writes three ticks after the caller starts. -/
  writes : ∀ port ∈ worker.ports,
    (timeOfPair (worker.writeToken port).time).value = startClock caller + 3
  /-- The caller finishes at tick four, after the worker writes. -/
  finish : finishClock caller = startClock caller + 4

end Airbender.Delegation.Caller
