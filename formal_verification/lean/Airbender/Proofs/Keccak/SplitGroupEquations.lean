import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitThetaRhoCached
import Airbender.Review.Circuits.Keccak.SplitChi5
import Airbender.Review.Circuits.Keccak.SplitChi5Cached
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

namespace Airbender.Keccak.Split.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- The first theta/rho grouped read is the control register. Its native
distance is one four-slot invocation when the worker is active. -/
theorem theta_rho_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup)) :
    let group := ThetaRho.importedConstraintsTimestampGroups[0]
    let columns := ThetaRho.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * w group.borrow = 0 ∧
    w group.previous[1] - w columns.invocation[1] + w group.borrow = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRho.importedConstraints setup)
      ThetaRho.importedConstraintsTimestampLookups)
  have low := Verification.assertion_of_holds core
    ⟨23, by simp [ThetaRho.importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds core
    ⟨24, by simp [ThetaRho.importedConstraints, FlatOperation.constraints]⟩
  constructor
  · simpa [ThetaRho.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      ThetaRho.importedConstraintsTimestampGroups,
      ThetaRho.importedConstraintsDelegationColumns,
      Trace.timestampBase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using low
  · simpa [ThetaRho.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      ThetaRho.importedConstraintsTimestampGroups,
      ThetaRho.importedConstraintsDelegationColumns,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using high


/-- The first ThetaRhoCached grouped read is the control register, one four-slot
invocation before an active worker's write. -/
theorem theta_rho_cached_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup)) :
    let group := ThetaRhoCached.importedConstraintsTimestampGroups[0]
    let columns := ThetaRhoCached.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * w group.borrow = 0 ∧
    w group.previous[1] - w columns.invocation[1] + w group.borrow = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRhoCached.importedConstraints setup)
      ThetaRhoCached.importedConstraintsTimestampLookups)
  have low := Verification.assertion_of_holds core
    ⟨23, by simp [ThetaRhoCached.importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds core
    ⟨24, by simp [ThetaRhoCached.importedConstraints, FlatOperation.constraints]⟩
  constructor
  · simpa [ThetaRhoCached.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      ThetaRhoCached.importedConstraintsTimestampGroups,
      ThetaRhoCached.importedConstraintsDelegationColumns,
      Trace.timestampBase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using low
  · simpa [ThetaRhoCached.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      ThetaRhoCached.importedConstraintsTimestampGroups,
      ThetaRhoCached.importedConstraintsDelegationColumns,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using high

/-- The first Chi5 grouped read is the control register, one four-slot
invocation before an active worker's write. -/
theorem chi5_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup)) :
    let group := Chi5.importedConstraintsTimestampGroups[0]
    let columns := Chi5.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * w group.borrow = 0 ∧
    w group.previous[1] - w columns.invocation[1] + w group.borrow = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5.importedConstraints setup)
      Chi5.importedConstraintsTimestampLookups)
  have low := Verification.assertion_of_holds core
    ⟨3, by simp [Chi5.importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds core
    ⟨4, by simp [Chi5.importedConstraints, FlatOperation.constraints]⟩
  constructor
  · simpa [Chi5.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      Chi5.importedConstraintsTimestampGroups,
      Chi5.importedConstraintsDelegationColumns,
      Trace.timestampBase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using low
  · simpa [Chi5.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      Chi5.importedConstraintsTimestampGroups,
      Chi5.importedConstraintsDelegationColumns,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using high

/-- The first Chi5Cached grouped read is the control register, one four-slot
invocation before an active worker's write. -/
theorem chi5_cached_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup)) :
    let group := Chi5Cached.importedConstraintsTimestampGroups[0]
    let columns := Chi5Cached.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * w group.borrow = 0 ∧
    w group.previous[1] - w columns.invocation[1] + w group.borrow = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5Cached.importedConstraints setup)
      Chi5Cached.importedConstraintsTimestampLookups)
  have low := Verification.assertion_of_holds core
    ⟨3, by simp [Chi5Cached.importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds core
    ⟨4, by simp [Chi5Cached.importedConstraints, FlatOperation.constraints]⟩
  constructor
  · simpa [Chi5Cached.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      Chi5Cached.importedConstraintsTimestampGroups,
      Chi5Cached.importedConstraintsDelegationColumns,
      Trace.timestampBase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using low
  · simpa [Chi5Cached.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      Chi5Cached.importedConstraintsTimestampGroups,
      Chi5Cached.importedConstraintsDelegationColumns,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using high


theorem theta_rho_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup)) :
    let group := ThetaRho.importedConstraintsTimestampGroups[0]
    w group.borrow * (w group.borrow - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRho.importedConstraints setup)
      ThetaRho.importedConstraintsTimestampLookups)
  have bit := Verification.assertion_of_holds core
    ⟨35, by simp [ThetaRho.importedConstraints, FlatOperation.constraints]⟩
  simpa [ThetaRho.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment,
    ThetaRho.importedConstraintsTimestampGroups, sub_eq_add_neg] using bit

theorem theta_rho_cached_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup)) :
    let group := ThetaRhoCached.importedConstraintsTimestampGroups[0]
    w group.borrow * (w group.borrow - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRhoCached.importedConstraints setup)
      ThetaRhoCached.importedConstraintsTimestampLookups)
  have bit := Verification.assertion_of_holds core
    ⟨35, by simp [ThetaRhoCached.importedConstraints, FlatOperation.constraints]⟩
  simpa [ThetaRhoCached.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment,
    ThetaRhoCached.importedConstraintsTimestampGroups, sub_eq_add_neg] using bit

theorem chi5_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup)) :
    let group := Chi5.importedConstraintsTimestampGroups[0]
    w group.borrow * (w group.borrow - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5.importedConstraints setup)
      Chi5.importedConstraintsTimestampLookups)
  have bit := Verification.assertion_of_holds core
    ⟨15, by simp [Chi5.importedConstraints, FlatOperation.constraints]⟩
  simpa [Chi5.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment,
    Chi5.importedConstraintsTimestampGroups, sub_eq_add_neg] using bit

theorem chi5_cached_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup)) :
    let group := Chi5Cached.importedConstraintsTimestampGroups[0]
    w group.borrow * (w group.borrow - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5Cached.importedConstraints setup)
      Chi5Cached.importedConstraintsTimestampLookups)
  have bit := Verification.assertion_of_holds core
    ⟨15, by simp [Chi5Cached.importedConstraints, FlatOperation.constraints]⟩
  simpa [Chi5Cached.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment,
    Chi5Cached.importedConstraintsTimestampGroups, sub_eq_add_neg] using bit

end Airbender.Keccak.Split.Proofs
