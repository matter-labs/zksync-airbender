module
public import Human.Circuits.KeccakSplit.Native
public import Proven.Delegation.NativeInvocation

@[expose] public section
namespace Airbender.Keccak.Split.Native.Proofs
open Airbender
set_option maxRecDepth 16384

private theorem columnParity_rejected {w : Nat → ZMod babyBearModulus}
    (active : w 0 = 1) (zero : w 1 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ColumnParity.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro constraints
  have query := Trace.Proofs.range_bound (Verification.lookup_of_holds constraints ⟨0, by decide +kernel⟩)
  norm_num [ColumnParity.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, active, zero] at query
  all_goals exact absurd query (by decide)

private theorem thetaRho_rejected {w : Nat → ZMod babyBearModulus}
    (active : w 0 = 1) (zero : w 1 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro constraints
  have query := Trace.Proofs.range_bound (Verification.lookup_of_holds constraints ⟨0, by decide +kernel⟩)
  norm_num [ThetaRho.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, active, zero] at query
  all_goals exact absurd query (by decide)

private theorem chi5_rejected {w : Nat → ZMod babyBearModulus}
    (active : w 0 = 1) (zero : w 1 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  intro constraints
  have query := Trace.Proofs.range_bound (Verification.lookup_of_holds constraints ⟨0, by decide +kernel⟩)
  norm_num [Chi5.importedConstraintsTimestampLookups, FlatOperation.lookups,
    Expression.eval, Verification.environment, active, zero] at query
  all_goals exact absurd query (by decide)

/-- Each active split-worker invocation has a nonzero raw clock. -/
theorem active_invocation_live {row : Row babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints)
    (active : row.assignment row.columns.execute = 1) :
    Trace.rawPair row.assignment row.columns.invocation ≠ (0, 0) := by
  intro zero
  have low := congrArg Prod.fst zero
  obtain ⟨kind, w⟩ := row
  cases kind
  all_goals change w 0 = 1 at active
  all_goals change w 1 = 0 at low
  · exact columnParity_rejected active low
      (Verification.holds_of_sublist constraints (List.sublist_append_right _ _))
  · exact thetaRho_rejected active low
      (Verification.holds_of_sublist constraints (List.sublist_append_right _ _))
  · exact chi5_rejected active low
      (Verification.holds_of_sublist constraints (List.sublist_append_right _ _))

end Airbender.Keccak.Split.Native.Proofs
