import Airbender.Review.Trace.Workers.Keccak.SplitNative
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Keccak.SplitGroupEquations
import Airbender.Proofs.Keccak.SplitGroupedOrder
import Airbender.Review.Helpers.Core.FieldCapacity

namespace Airbender.Keccak.Split.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- The theta/rho controller lookup yields exactly one live iteration flag for
an active row. The statement uses the actual five witness columns selected by
the native grouped distance equations. -/
theorem theta_rho_control_selector [Fact p.Prime]
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup.thetaRho)) (active : w 0 = 1) :
    ∃ selected : Fin 5, ∀ index : Fin 5,
      w (84 + index.val) = if index = selected then 1 else 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRho.importedConstraints setup.thetaRho)
      ThetaRho.importedConstraintsTimestampLookups)
  let query := (FlatOperation.lookups (ThetaRho.importedConstraints setup.thetaRho)).get
    ⟨9, by simp [ThetaRho.importedConstraints, FlatOperation.lookups]⟩
  have lookup : query.Contains (Verification.environment w) :=
    Verification.lookup_of_holds core _
  have sound := query.table.imply_soundness _ _ lookup
  let row : Vector (ZMod p) 9 :=
    query.entry.map (Expression.eval (Verification.environment w))
  have rowSound : setup.thetaRho.toRaw.Soundness #[] row := by
    change setup.thetaRho.toRaw.Soundness #[] row at sound
    exact sound
  have tag : row[8] = 59 := by
    simp [row, query, ThetaRho.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  have enabled : row[1] = 1 := by
    simpa [row, query, ThetaRho.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using active
  obtain ⟨selected, flags⟩ := control.thetaRho row rowSound tag enabled
  refine ⟨selected, ?_⟩
  intro index
  have flag := flags index
  fin_cases index <;>
    simpa [row, query, ThetaRho.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using flag

/-- The fixed chi5 controller row bounds the row index used in all six native
group distances. Its table semantics are an explicit public setup premise. -/
theorem chi5_control_row_bound [Fact p.Prime]
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup.chi5)) (active : w 0 = 1) :
    (w 54).val < 5 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5.importedConstraints setup.chi5)
      Chi5.importedConstraintsTimestampLookups)
  let query := (FlatOperation.lookups (Chi5.importedConstraints setup.chi5)).get
    ⟨0, by simp [Chi5.importedConstraints, FlatOperation.lookups]⟩
  have lookup : query.Contains (Verification.environment w) :=
    Verification.lookup_of_holds core _
  have sound := query.table.imply_soundness _ _ lookup
  let row : Vector (ZMod p) 11 :=
    query.entry.map (Expression.eval (Verification.environment w))
  have rowSound : setup.chi5.toRaw.Soundness #[] row := by
    change setup.chi5.toRaw.Soundness #[] row at sound
    exact sound
  have tag : row[10] = 66 := by
    simp [row, query, Chi5.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  have enabled : row[1] = 1 := by
    simpa [row, query, Chi5.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using active
  have index : row[8] = w 54 := by
    simp [row, query, Chi5.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  simpa only [index] using control.chi5 row rowSound tag enabled


theorem theta_rho_cached_control_selector [Fact p.Prime]
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup.thetaRho)) (active : w 0 = 1) :
    ∃ selected : Fin 5, ∀ index : Fin 5,
      w (84 + index.val) = if index = selected then 1 else 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRhoCached.importedConstraints setup.thetaRho)
      ThetaRhoCached.importedConstraintsTimestampLookups)
  let query := (FlatOperation.lookups (ThetaRhoCached.importedConstraints setup.thetaRho)).get
    ⟨9, by simp [ThetaRhoCached.importedConstraints, FlatOperation.lookups]⟩
  have lookup : query.Contains (Verification.environment w) :=
    Verification.lookup_of_holds core _
  have sound := query.table.imply_soundness _ _ lookup
  let row : Vector (ZMod p) 9 :=
    query.entry.map (Expression.eval (Verification.environment w))
  have rowSound : setup.thetaRho.toRaw.Soundness #[] row := by
    change setup.thetaRho.toRaw.Soundness #[] row at sound
    exact sound
  have tag : row[8] = 59 := by
    simp [row, query, ThetaRhoCached.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  have enabled : row[1] = 1 := by
    simpa [row, query, ThetaRhoCached.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using active
  obtain ⟨selected, flags⟩ := control.thetaRho row rowSound tag enabled
  refine ⟨selected, ?_⟩
  intro index
  have flag := flags index
  fin_cases index <;>
    simpa [row, query, ThetaRhoCached.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using flag

theorem chi5_cached_control_row_bound [Fact p.Prime]
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup.chi5)) (active : w 0 = 1) :
    (w 54).val < 5 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5Cached.importedConstraints setup.chi5)
      Chi5Cached.importedConstraintsTimestampLookups)
  let query := (FlatOperation.lookups (Chi5Cached.importedConstraints setup.chi5)).get
    ⟨0, by simp [Chi5Cached.importedConstraints, FlatOperation.lookups]⟩
  have lookup : query.Contains (Verification.environment w) :=
    Verification.lookup_of_holds core _
  have sound := query.table.imply_soundness _ _ lookup
  let row : Vector (ZMod p) 11 :=
    query.entry.map (Expression.eval (Verification.environment w))
  have rowSound : setup.chi5.toRaw.Soundness #[] row := by
    change setup.chi5.toRaw.Soundness #[] row at sound
    exact sound
  have tag : row[10] = 66 := by
    simp [row, query, Chi5Cached.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  have enabled : row[1] = 1 := by
    simpa [row, query, Chi5Cached.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using active
  have index : row[8] = w 54 := by
    simp [row, query, Chi5Cached.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  simpa only [index] using control.chi5 row rowSound tag enabled

/-- Every active theta/rho grouped distance is one of the source constants
1, 2, 3, 4, 5 or 6. The one-hot fact comes from the fixed controller table. -/
theorem theta_rho_distance_nat [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 6)
    {w : Nat → ZMod p} (active : w 0 = 1)
    (selector : ∃ selected : Fin 5, ∀ index : Fin 5,
      w (84 + index.val) = if index = selected then 1 else 0)
    (i : Fin 4) :
    ∃ distance : Nat, 0 < distance ∧
      4 * distance < Trace.timestampBase ∧
      (thetaRhoDistance w)[i] = (distance : ZMod p) := by
  obtain ⟨selected, flags⟩ := selector
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f4 := flags 4
  have v1 : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := p) (a := 1) (by omega)
  have v2 : (2 : ZMod p).val = 2 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 2) (by omega)
  have v3 : (3 : ZMod p).val = 3 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 3) (by omega)
  have v4 : (4 : ZMod p).val = 4 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 4) (by omega)
  have v5 : (5 : ZMod p).val = 5 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 5) (by omega)
  have v6 : (6 : ZMod p).val = 6 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 6) (by omega)
  have bounds : 0 < ((thetaRhoDistance w)[i]).val ∧
      4 * ((thetaRhoDistance w)[i]).val < Trace.timestampBase := by
    fin_cases selected
    all_goals simp at f0 f1 f2 f3 f4
    all_goals fin_cases i
    all_goals simp [thetaRhoDistance, active, f0, f1, f2, f3, f4,
      v1, v2, v3, v4, v5, v6, Trace.timestampBase]
  exact ⟨((thetaRhoDistance w)[i]).val, bounds.1, bounds.2,
    (ZMod.natCast_zmod_val _).symm⟩

/-- The active chi5 controller's row index is below five, so every grouped
distance is a positive number of four-slot calls with no field wrap. -/
theorem chi5_distance_nat [Fact p.Prime]
    (_hp : FieldCapacity.NoWrap p 10)
    {w : Nat → ZMod p} (active : w 0 = 1)
    (rowBound : (w 54).val < 5) (i : Fin 6) :
    ∃ distance : Nat, 0 < distance ∧
      4 * distance < Trace.timestampBase ∧
      (chi5Distance w)[i] = (distance : ZMod p) := by
  fin_cases i
  · exact ⟨1, by decide, by decide, by simp [chi5Distance, active]⟩
  · refine ⟨5 + (w 54).val, by omega, by norm_num [Trace.timestampBase]; omega, ?_⟩
    simp [chi5Distance, active, Nat.cast_add]
  · refine ⟨4 + (w 54).val, by omega, by norm_num [Trace.timestampBase]; omega, ?_⟩
    simp [chi5Distance, active, Nat.cast_add]
  · refine ⟨3 + (w 54).val, by omega, by norm_num [Trace.timestampBase]; omega, ?_⟩
    simp [chi5Distance, active, Nat.cast_add]
  · refine ⟨2 + (w 54).val, by omega, by norm_num [Trace.timestampBase]; omega, ?_⟩
    simp [chi5Distance, active, Nat.cast_add]
  · refine ⟨1 + (w 54).val, by omega, by norm_num [Trace.timestampBase]; omega, ?_⟩
    simp [chi5Distance, active, Nat.cast_add]

/-- The public controller table and the imported grouped equations establish
strict order for each theta/rho read once logical RAM matching bounds it. -/
theorem theta_rho_group_order [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup.thetaRho)) (active : w 0 = 1)
    (i : Fin 4)
    (initial : (Trace.decodeTimestamp w
      ThetaRho.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      ThetaRho.importedConstraintsTimestampGroups[i].previous).Bounded) :
    (Trace.decodeTimestamp w
      ThetaRho.importedConstraintsTimestampGroups[i].previous).value <
      (Trace.decodeTimestamp w
        ThetaRho.importedConstraintsDelegationColumns.invocation).value + 2 := by
  obtain ⟨distance, positive, small, same⟩ := theta_rho_distance_nat
    (by dsimp [FieldCapacity.ClockNoWrap, Trace.timestampBase] at hp; omega) active
    (theta_rho_control_selector control h active) i
  obtain ⟨low, high, bit⟩ := theta_rho_group_clocks h i
  have lower :
      ((Trace.decodeTimestamp w
          ThetaRho.importedConstraintsTimestampGroups[i].previous).lo : ZMod p) -
        ((Trace.decodeTimestamp w
          ThetaRho.importedConstraintsDelegationColumns.invocation).lo : ZMod p) - 2 +
        ((4 * distance : Nat) : ZMod p) -
        (Trace.timestampBase : ZMod p) *
          (ThetaRho.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val,
      ThetaRho.importedConstraintsDelegationColumns, active, same,
      Nat.cast_mul] using low
  have upper :
      ((Trace.decodeTimestamp w
          ThetaRho.importedConstraintsTimestampGroups[i].previous).hi : ZMod p) -
        ((Trace.decodeTimestamp w
          ThetaRho.importedConstraintsDelegationColumns.invocation).hi : ZMod p) +
        (ThetaRho.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val] using high
  exact grouped_distance_order hp initial previous positive small bit lower upper


theorem theta_rho_cached_group_order [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup.thetaRho)) (active : w 0 = 1)
    (i : Fin 4)
    (initial : (Trace.decodeTimestamp w
      ThetaRhoCached.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      ThetaRhoCached.importedConstraintsTimestampGroups[i].previous).Bounded) :
    (Trace.decodeTimestamp w
      ThetaRhoCached.importedConstraintsTimestampGroups[i].previous).value <
      (Trace.decodeTimestamp w
        ThetaRhoCached.importedConstraintsDelegationColumns.invocation).value + 2 := by
  obtain ⟨distance, positive, small, same⟩ := theta_rho_distance_nat
    (by dsimp [FieldCapacity.ClockNoWrap, Trace.timestampBase] at hp; omega) active
    (theta_rho_cached_control_selector control h active) i
  obtain ⟨low, high, bit⟩ := theta_rho_cached_group_clocks h i
  have lower :
      ((Trace.decodeTimestamp w
          ThetaRhoCached.importedConstraintsTimestampGroups[i].previous).lo : ZMod p) -
        ((Trace.decodeTimestamp w
          ThetaRhoCached.importedConstraintsDelegationColumns.invocation).lo : ZMod p) - 2 +
        ((4 * distance : Nat) : ZMod p) -
        (Trace.timestampBase : ZMod p) *
          (ThetaRhoCached.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val,
      ThetaRhoCached.importedConstraintsDelegationColumns, active, same,
      Nat.cast_mul] using low
  have upper :
      ((Trace.decodeTimestamp w
          ThetaRhoCached.importedConstraintsTimestampGroups[i].previous).hi : ZMod p) -
        ((Trace.decodeTimestamp w
          ThetaRhoCached.importedConstraintsDelegationColumns.invocation).hi : ZMod p) +
        (ThetaRhoCached.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val] using high
  exact grouped_distance_order hp initial previous positive small bit lower upper

theorem chi5_group_order [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup.chi5)) (active : w 0 = 1)
    (i : Fin 6)
    (initial : (Trace.decodeTimestamp w
      Chi5.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      Chi5.importedConstraintsTimestampGroups[i].previous).Bounded) :
    (Trace.decodeTimestamp w
      Chi5.importedConstraintsTimestampGroups[i].previous).value <
      (Trace.decodeTimestamp w
        Chi5.importedConstraintsDelegationColumns.invocation).value + 2 := by
  obtain ⟨distance, positive, small, same⟩ := chi5_distance_nat
    (by dsimp [FieldCapacity.ClockNoWrap, Trace.timestampBase] at hp; omega) active
    (chi5_control_row_bound control h active) i
  obtain ⟨low, high, bit⟩ := chi5_group_clocks h i
  have lower :
      ((Trace.decodeTimestamp w
          Chi5.importedConstraintsTimestampGroups[i].previous).lo : ZMod p) -
        ((Trace.decodeTimestamp w
          Chi5.importedConstraintsDelegationColumns.invocation).lo : ZMod p) - 2 +
        ((4 * distance : Nat) : ZMod p) -
        (Trace.timestampBase : ZMod p) *
          (Chi5.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val,
      Chi5.importedConstraintsDelegationColumns, active, same,
      Nat.cast_mul] using low
  have upper :
      ((Trace.decodeTimestamp w
          Chi5.importedConstraintsTimestampGroups[i].previous).hi : ZMod p) -
        ((Trace.decodeTimestamp w
          Chi5.importedConstraintsDelegationColumns.invocation).hi : ZMod p) +
        (Chi5.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val] using high
  exact grouped_distance_order hp initial previous positive small bit lower upper

theorem chi5_cached_group_order [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup.chi5)) (active : w 0 = 1)
    (i : Fin 6)
    (initial : (Trace.decodeTimestamp w
      Chi5Cached.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      Chi5Cached.importedConstraintsTimestampGroups[i].previous).Bounded) :
    (Trace.decodeTimestamp w
      Chi5Cached.importedConstraintsTimestampGroups[i].previous).value <
      (Trace.decodeTimestamp w
        Chi5Cached.importedConstraintsDelegationColumns.invocation).value + 2 := by
  obtain ⟨distance, positive, small, same⟩ := chi5_distance_nat
    (by dsimp [FieldCapacity.ClockNoWrap, Trace.timestampBase] at hp; omega) active
    (chi5_cached_control_row_bound control h active) i
  obtain ⟨low, high, bit⟩ := chi5_cached_group_clocks h i
  have lower :
      ((Trace.decodeTimestamp w
          Chi5Cached.importedConstraintsTimestampGroups[i].previous).lo : ZMod p) -
        ((Trace.decodeTimestamp w
          Chi5Cached.importedConstraintsDelegationColumns.invocation).lo : ZMod p) - 2 +
        ((4 * distance : Nat) : ZMod p) -
        (Trace.timestampBase : ZMod p) *
          (Chi5Cached.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val,
      Chi5Cached.importedConstraintsDelegationColumns, active, same,
      Nat.cast_mul] using low
  have upper :
      ((Trace.decodeTimestamp w
          Chi5Cached.importedConstraintsTimestampGroups[i].previous).hi : ZMod p) -
        ((Trace.decodeTimestamp w
          Chi5Cached.importedConstraintsDelegationColumns.invocation).hi : ZMod p) +
        (Chi5Cached.importedConstraintsTimestampGroups[i]).borrowValue w = 0 := by
    simpa [Trace.decodeTimestamp, ZMod.natCast_zmod_val] using high
  exact grouped_distance_order hp initial previous positive small bit lower upper

end Airbender.Keccak.Split.Proofs
