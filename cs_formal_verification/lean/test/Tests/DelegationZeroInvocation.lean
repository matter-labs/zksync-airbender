module
public import Human.Helpers.Delegation.WorkerContext
public import Slop.Delegation.Operations
public import Slop.Delegation.Requests
public import Slop.Delegation.PortEvents
public import Slop.CleanCore.Circuit.Operations

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

private theorem keccak_rejected {w : Nat → ZMod babyBearModulus} (active : w 0 = 1) (zero : w 1 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro h
  have query := Trace.Proofs.range_bound (Verification.lookup_of_holds h
    ⟨0, by rw [Keccak.timestamp_count]; decide⟩)
  norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, active, zero] at query
  all_goals exact absurd query (by decide)

private theorem bigint_rejected {w : Nat → ZMod babyBearModulus} (active : w 0 = 1) (zero : w 1 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro h
  have query := Trace.Proofs.range_bound (Verification.lookup_of_holds h
    ⟨0, by rw [Bigint.timestamp_count]; decide⟩)
  norm_num [Bigint.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, active, zero] at query
  all_goals exact absurd query (by decide)

private theorem blakeG_rejected {w : Nat → ZMod babyBearModulus} (active : w 0 = 1) (zero : w 1 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro h
  have query := Trace.Proofs.range_bound (Verification.lookup_of_holds h
    ⟨0, by rw [Blake2G.timestamp_count]; decide⟩)
  norm_num [Blake2G.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, active, zero] at query
  all_goals exact absurd query (by decide)

private theorem blakeRound_rejected {w : Nat → ZMod babyBearModulus} (active : w 0 = 1) (zero : w 1 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro h
  have query := Trace.Proofs.range_bound (Verification.lookup_of_holds h
    ⟨0, by rw [Blake2Round.timestamp_count]; decide⟩)
  norm_num [Blake2Round.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, active, zero] at query
  all_goals exact absurd query (by decide)

/-- No delegation family accepts an active row whose invocation low limb is zero,
    for any setup tables: the zero-clock fulfillment cannot come from an active worker. -/
theorem active_zero_invocation_rejected (row : Delegation.Row babyBearModulus)
    (setup : Delegation.Setup babyBearModulus)
    (active : row.assignment row.columns.execute = 1)
    (zero : row.assignment row.columns.invocation[0] = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup) := by
  obtain ⟨family, w⟩ := row
  intro h
  cases family
  · rw [show Delegation.Row.columns ⟨.bigint, w⟩ = Bigint.importedConstraintsDelegationColumns from rfl,
      Bigint.delegation_columns] at active zero
    exact bigint_rejected active zero (Verification.holds_of_sublist h (List.sublist_append_right _ _))
  · rw [show Delegation.Row.columns ⟨.blakeG, w⟩ = Blake2G.importedConstraintsDelegationColumns from rfl,
      Blake2G.delegation_columns] at active zero
    exact blakeG_rejected active zero (Verification.holds_of_sublist h (List.sublist_append_right _ _))
  · rw [show Delegation.Row.columns ⟨.blakeRound, w⟩ = Blake2Round.importedConstraintsDelegationColumns from rfl,
      Blake2Round.delegation_columns] at active zero
    exact blakeRound_rejected active zero (Verification.holds_of_sublist h (List.sublist_append_right _ _))
  · rw [show Delegation.Row.columns ⟨.keccak, w⟩ = Keccak.importedConstraintsDelegationColumns from rfl,
      Keccak.delegation_columns] at active zero
    exact keccak_rejected active zero (Verification.holds_of_sublist h (List.sublist_append_right _ _))

/-- Inactive rows still admit the zero clock: query 0 is `(0 - 0) / 4 = 0`. -/
theorem inactive_zero_invocation_query (w : Nat → ZMod babyBearModulus) (inactive : w 0 = 0)
    (zero : w 1 = 0) :
    ((FlatOperation.lookups (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus))).get
      ⟨0, by rw [Keccak.timestamp_count]; decide⟩).Contains (Verification.environment w) := by
  apply Trace.Proofs.range_contains
  norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, inactive, zero, Trace.timestampBase]

end Tests.DelegationZeroInvocation
