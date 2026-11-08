module
public import Human.Helpers.Context.Columns

@[expose] public section

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

/-- One shared read timestamp of a split Keccak worker (theta/rho, chi5): the
    native `members` ports all read at `previous`. These circuits commit no borrow
    column: their equations use `invocationHigh - previous[1]` as the borrow
    (`borrowValue`). The descriptor itself asserts no timing relation. -/
structure GroupedTimestamp where
  previous : Vector Nat 2
  invocationHigh : Nat
  members : Array Nat
  deriving DecidableEq

def GroupedTimestamp.borrowValue {F : Type} [Sub F] (group : GroupedTimestamp) (w : Nat → F) : F :=
  w group.invocationHigh - w group.previous[1]

end Airbender.Delegation
