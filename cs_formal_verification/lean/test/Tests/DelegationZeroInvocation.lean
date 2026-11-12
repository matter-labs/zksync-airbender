module
public import Proven.Delegation.NativeInvocation
public import Human.Helpers.Delegation.WorkerContext
public import Proven.Delegation.Operations
public import Proven.Delegation.Requests
public import Proven.Delegation.PortEvents
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

/-! The upstream delegation circuits range-check `(invocation-low - execute) / 4`
    (timestamp query 0 of every family). An active worker (`execute = 1`) with a
    zero invocation clock would need `-1/4` in the 19-bit table, so the circuit
    itself rejects the zero-clock worker that the previous fixture accepted (an
    unissued worker invisible to request matching). The regression is inverted:
    every delegation family rejects an active row whose invocation low limb is zero. -/

namespace Tests.DelegationZeroInvocation
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

/-- Every active standard worker rejects a zero invocation clock. -/
theorem active_zero_invocation_rejected (row : Delegation.Row babyBearModulus)
    (setup : Delegation.Setup babyBearModulus) (active : row.assignment row.columns.execute = 1)
    (zero : row.assignment row.columns.invocation[0] = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup) :=
  Delegation.Proofs.active_zero_invocation_rejected row setup active zero

/-- Inactive rows still admit the zero clock: query 0 is `(0 - 0) / 4 = 0`. -/
theorem inactive_zero_invocation_query (w : Nat → ZMod babyBearModulus) (inactive : w 0 = 0)
    (zero : w 1 = 0) :
    ((FlatOperation.lookups (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus))).get
      ⟨0, by rw [Keccak.timestamp_count]; decide⟩).Contains (Verification.environment w) := by
  apply Trace.Proofs.range_contains
  norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, inactive, zero, Trace.timestampBase]

end Tests.DelegationZeroInvocation
