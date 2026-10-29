import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitThetaRhoCached
import Airbender.Review.Circuits.Keccak.SplitChi5
import Airbender.Review.Circuits.Keccak.SplitChi5Cached
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.LinearCombination

namespace Airbender.Keccak.Split.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- Exact four-call distances emitted by the theta/rho compiler. The control
lookup must separately establish which selector is live. -/
def thetaRhoDistance (w : Nat → ZMod p) : Vector (ZMod p) 4 :=
  #v[w 0, 5 * w 0,
    w 84 + 6 * w 85 + 2 * w 86 + 2 * w 87 + 2 * w 88,
    4 * w 84 + 4 * w 85 + 4 * w 86 + 3 * w 87 + 3 * w 88]

/-- Exact six-call distances emitted by the chi5 compiler. The control lookup
must separately bound and identify the row index in column 54. -/
def chi5Distance (w : Nat → ZMod p) : Vector (ZMod p) 6 :=
  #v[w 0, 5 * w 0 + w 54, 4 * w 0 + w 54, 3 * w 0 + w 54,
    2 * w 0 + w 54, w 0 + w 54]

/-- The native low equation and Boolean derived borrow imply the grouped
clock equations. The high equation follows from the borrow definition. -/
theorem theta_rho_group_clocks [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup)) (i : Fin 4) :
    let group := ThetaRho.importedConstraintsTimestampGroups[i]
    let columns := ThetaRho.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      (4 : ZMod p) * (thetaRhoDistance w)[i] -
        (Trace.timestampBase : ZMod p) * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 ∧
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRho.importedConstraints setup)
      ThetaRho.importedConstraintsTimestampLookups)
  have bound : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by
    rfl
  have low := Verification.assertion_of_holds core
    ⟨23 + 2 * i.val, by rw [bound]; omega⟩
  have bit := Verification.assertion_of_holds core
    ⟨24 + 2 * i.val, by rw [bound]; omega⟩
  fin_cases i
  all_goals
    constructor
    · simp [ThetaRho.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      ThetaRho.importedConstraintsTimestampGroups,
      ThetaRho.importedConstraintsDelegationColumns,
      Delegation.GroupedTimestamp.borrowValue, thetaRhoDistance, Trace.timestampBase,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] at low ⊢
      linear_combination low
    · constructor
      · simp [ThetaRho.importedConstraintsTimestampGroups,
          ThetaRho.importedConstraintsDelegationColumns,
          Delegation.GroupedTimestamp.borrowValue]
      · simpa [ThetaRho.importedConstraints, FlatOperation.constraints,
          Expression.eval, Verification.environment,
          ThetaRho.importedConstraintsTimestampGroups,
          Delegation.GroupedTimestamp.borrowValue, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using bit

/-- The control-register read has one four-slot invocation distance. -/
theorem theta_rho_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup)) :
    let group := ThetaRho.importedConstraintsTimestampGroups[0]
    let columns := ThetaRho.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 := by
  have facts := theta_rho_group_clocks h 0
  simpa [thetaRhoDistance, ThetaRho.importedConstraintsDelegationColumns] using
    And.intro facts.1 facts.2.1

/-- Booleanity applies to the high-limb difference. No borrow witness is committed. -/
theorem theta_rho_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup)) :
    let group := ThetaRho.importedConstraintsTimestampGroups[0]
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  exact (theta_rho_group_clocks h 0).2.2

/-- The native low equation and Boolean derived borrow imply the grouped
clock equations. The high equation follows from the borrow definition. -/
theorem theta_rho_cached_group_clocks [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup)) (i : Fin 4) :
    let group := ThetaRhoCached.importedConstraintsTimestampGroups[i]
    let columns := ThetaRhoCached.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      (4 : ZMod p) * (thetaRhoDistance w)[i] -
        (Trace.timestampBase : ZMod p) * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 ∧
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRhoCached.importedConstraints setup)
      ThetaRhoCached.importedConstraintsTimestampLookups)
  have bound : (FlatOperation.constraints (ThetaRhoCached.importedConstraints setup)).length = 35 := by
    rfl
  have low := Verification.assertion_of_holds core
    ⟨23 + 2 * i.val, by rw [bound]; omega⟩
  have bit := Verification.assertion_of_holds core
    ⟨24 + 2 * i.val, by rw [bound]; omega⟩
  fin_cases i
  all_goals
    constructor
    · simp [ThetaRhoCached.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      ThetaRhoCached.importedConstraintsTimestampGroups,
      ThetaRhoCached.importedConstraintsDelegationColumns,
      Delegation.GroupedTimestamp.borrowValue, thetaRhoDistance, Trace.timestampBase,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] at low ⊢
      linear_combination low
    · constructor
      · simp [ThetaRhoCached.importedConstraintsTimestampGroups,
          ThetaRhoCached.importedConstraintsDelegationColumns,
          Delegation.GroupedTimestamp.borrowValue]
      · simpa [ThetaRhoCached.importedConstraints, FlatOperation.constraints,
          Expression.eval, Verification.environment,
          ThetaRhoCached.importedConstraintsTimestampGroups,
          Delegation.GroupedTimestamp.borrowValue, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using bit

/-- The control-register read has one four-slot invocation distance. -/
theorem theta_rho_cached_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup)) :
    let group := ThetaRhoCached.importedConstraintsTimestampGroups[0]
    let columns := ThetaRhoCached.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 := by
  have facts := theta_rho_cached_group_clocks h 0
  simpa [thetaRhoDistance, ThetaRhoCached.importedConstraintsDelegationColumns] using
    And.intro facts.1 facts.2.1

/-- Booleanity applies to the high-limb difference. No borrow witness is committed. -/
theorem theta_rho_cached_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup)) :
    let group := ThetaRhoCached.importedConstraintsTimestampGroups[0]
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  exact (theta_rho_cached_group_clocks h 0).2.2

/-- The native low equation and Boolean derived borrow imply the grouped
clock equations. The high equation follows from the borrow definition. -/
theorem chi5_group_clocks [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup)) (i : Fin 6) :
    let group := Chi5.importedConstraintsTimestampGroups[i]
    let columns := Chi5.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      (4 : ZMod p) * (chi5Distance w)[i] -
        (Trace.timestampBase : ZMod p) * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 ∧
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5.importedConstraints setup)
      Chi5.importedConstraintsTimestampLookups)
  have bound : (FlatOperation.constraints (Chi5.importedConstraints setup)).length = 15 := by
    rfl
  have low := Verification.assertion_of_holds core
    ⟨3 + 2 * i.val, by rw [bound]; omega⟩
  have bit := Verification.assertion_of_holds core
    ⟨4 + 2 * i.val, by rw [bound]; omega⟩
  fin_cases i
  all_goals
    constructor
    · simp [Chi5.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      Chi5.importedConstraintsTimestampGroups,
      Chi5.importedConstraintsDelegationColumns,
      Delegation.GroupedTimestamp.borrowValue, chi5Distance, Trace.timestampBase,
      sub_eq_add_neg, add_assoc, add_comm] at low ⊢
      linear_combination low
    · constructor
      · simp [Chi5.importedConstraintsTimestampGroups,
          Chi5.importedConstraintsDelegationColumns,
          Delegation.GroupedTimestamp.borrowValue]
      · simpa [Chi5.importedConstraints, FlatOperation.constraints,
          Expression.eval, Verification.environment,
          Chi5.importedConstraintsTimestampGroups,
          Delegation.GroupedTimestamp.borrowValue, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using bit

/-- The control-register read has one four-slot invocation distance. -/
theorem chi5_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup)) :
    let group := Chi5.importedConstraintsTimestampGroups[0]
    let columns := Chi5.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 := by
  have facts := chi5_group_clocks h 0
  simpa [chi5Distance, Chi5.importedConstraintsDelegationColumns] using
    And.intro facts.1 facts.2.1

/-- Booleanity applies to the high-limb difference. No borrow witness is committed. -/
theorem chi5_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup)) :
    let group := Chi5.importedConstraintsTimestampGroups[0]
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  exact (chi5_group_clocks h 0).2.2

/-- The native low equation and Boolean derived borrow imply the grouped
clock equations. The high equation follows from the borrow definition. -/
theorem chi5_cached_group_clocks [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup)) (i : Fin 6) :
    let group := Chi5Cached.importedConstraintsTimestampGroups[i]
    let columns := Chi5Cached.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      (4 : ZMod p) * (chi5Distance w)[i] -
        (Trace.timestampBase : ZMod p) * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 ∧
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5Cached.importedConstraints setup)
      Chi5Cached.importedConstraintsTimestampLookups)
  have bound : (FlatOperation.constraints (Chi5Cached.importedConstraints setup)).length = 15 := by
    rfl
  have low := Verification.assertion_of_holds core
    ⟨3 + 2 * i.val, by rw [bound]; omega⟩
  have bit := Verification.assertion_of_holds core
    ⟨4 + 2 * i.val, by rw [bound]; omega⟩
  fin_cases i
  all_goals
    constructor
    · simp [Chi5Cached.importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment,
      Chi5Cached.importedConstraintsTimestampGroups,
      Chi5Cached.importedConstraintsDelegationColumns,
      Delegation.GroupedTimestamp.borrowValue, chi5Distance, Trace.timestampBase,
      sub_eq_add_neg, add_assoc, add_comm] at low ⊢
      linear_combination low
    · constructor
      · simp [Chi5Cached.importedConstraintsTimestampGroups,
          Chi5Cached.importedConstraintsDelegationColumns,
          Delegation.GroupedTimestamp.borrowValue]
      · simpa [Chi5Cached.importedConstraints, FlatOperation.constraints,
          Expression.eval, Verification.environment,
          Chi5Cached.importedConstraintsTimestampGroups,
          Delegation.GroupedTimestamp.borrowValue, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using bit

/-- The control-register read has one four-slot invocation distance. -/
theorem chi5_cached_register_clock [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup)) :
    let group := Chi5Cached.importedConstraintsTimestampGroups[0]
    let columns := Chi5Cached.importedConstraintsDelegationColumns
    w group.previous[0] - w columns.invocation[0] - 2 * w columns.execute +
      4 * w columns.execute - Trace.timestampBase * group.borrowValue w = 0 ∧
    w group.previous[1] - w columns.invocation[1] + group.borrowValue w = 0 := by
  have facts := chi5_cached_group_clocks h 0
  simpa [chi5Distance, Chi5Cached.importedConstraintsDelegationColumns] using
    And.intro facts.1 facts.2.1

/-- Booleanity applies to the high-limb difference. No borrow witness is committed. -/
theorem chi5_cached_register_borrow [Fact p.Prime]
    {setup : Table (ZMod p) (fields 11)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup)) :
    let group := Chi5Cached.importedConstraintsTimestampGroups[0]
    group.borrowValue w * (group.borrowValue w - 1) = 0 := by
  exact (chi5_cached_group_clocks h 0).2.2

end Airbender.Keccak.Split.Proofs
