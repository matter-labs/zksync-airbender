import Human.Helpers.Context.Columns

namespace Airbender.Delegation

/-- Clock metadata imported from a delegation layout. These circuits have an
    invocation clock, rather than an initial/final machine-state pair. All their
    native ports write at offset two; port order is not a sequence of distinct
    write times. `ports` retains every previous timestamp and comparison borrow. -/
structure ClockColumns where
  execute : Nat
  invocation : Vector Nat 2
  ports : Array Trace.TimestampPort
  deriving DecidableEq

end Airbender.Delegation
