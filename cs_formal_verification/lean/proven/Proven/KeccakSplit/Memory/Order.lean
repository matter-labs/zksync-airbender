module
public import Proven.KeccakSplit.Memory.GroupEquations
public import Proven.KeccakSplit.Memory.ParityClock
public import Human.Circuits.KeccakSplit.Native
public import Proven.Arithmetic.Lemmas
public import Proven.CleanCore.Circuit.Operations
public import Proven.Defs.Helpers.Delegation.Columns

@[expose] public section

/- Read-before-write order of every split-worker port (ported from PR #585's
   SplitGroupedOrder, SplitControlLookup and SplitPortOrder, no-cache only).
   Column parity compares each port's timestamp through range-checked borrows;
   theta/rho and chi5 fix each group's read time to a positive number of calls
   earlier, with the distance selected by the controller row. -/

namespace Airbender.Keccak.Split.Proofs
open Airbender.Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- The controller-row facts of the exported setup used by the grouped clocks:
    an enabled theta/rho controller row (tag 59) has a one-hot iteration selector,
    an enabled chi5 controller row (tag 66) has a row index below five. Proved
    from the decoded setup in Proven.KeccakSplit.Setup. -/
structure ControlFacts (p : Nat) [Fact p.Prime] : Prop where
  thetaRho : ∀ row : Vector (ZMod p) 9,
    (ThetaRho.setup (p := p)).toRaw.Soundness #[] row → row[8] = 59 → row[1] = 1 →
      ∃ selected : Fin 5, ∀ index : Fin 5,
        row[3 + index.val] = if index = selected then 1 else 0
  chi5 : ∀ row : Vector (ZMod p) 11,
    (Chi5.setup (p := p)).toRaw.Soundness #[] row → row[10] = 66 → row[1] = 1 →
      row[8].val < 5

theorem column_parity_memory_ports :
    ColumnParity.importedConstraintsMemoryPorts.size = 14 := by rfl

theorem theta_rho_memory_ports :
    ThetaRho.importedConstraintsMemoryPorts.size = 16 := by rfl

theorem chi5_memory_ports :
    Chi5.importedConstraintsMemoryPorts.size = 12 := by rfl

/-- Both emitted metadata arrays select the same clock descriptor for every port. -/
theorem split_port_clocks_match {p : Nat} (row : Native.Row p) :
    row.ports.map Airbender.Trace.MemoryPort.clock = row.columns.ports := by
  cases row with
  | mk kind assignment =>
    cases kind <;> simp only [Native.Row.ports, Native.Row.columns] <;> decide +kernel

/-- A positive grouped read distance gives strict order without a separate
timestamp lookup for every port in the group. -/
theorem grouped_distance_order [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p)
    {initial previous : Timestamp} (ib : initial.Bounded)
    (pb : previous.Bounded) {distance : Nat}
    (positive : 0 < distance) (small : 4 * distance < timestampBase)
    {borrow : ZMod p} (bit : borrow * (borrow - 1) = 0)
    (low : (previous.lo : ZMod p) - (initial.lo : ZMod p) - 2 +
      ((4 * distance : Nat) : ZMod p) - (timestampBase : ZMod p) * borrow = 0)
    (high : (previous.hi : ZMod p) - (initial.hi : ZMod p) + borrow = 0) :
    previous.value < initial.value + 2 := by
  obtain ⟨carry, cb, equation⟩ := Arithmetic.boolean_nat bit
  rw [equation] at low high
  have lowCast : ((previous.lo + 4 * distance : Nat) : ZMod p) =
      ((initial.lo + 2 + timestampBase * carry : Nat) : ZMod p) := by
    push_cast
    simp only [Nat.cast_mul] at low
    linear_combination low
  have highCast : ((previous.hi + carry : Nat) : ZMod p) =
      (initial.hi : ZMod p) := by
    push_cast
    linear_combination high
  have lowNat : previous.lo + 4 * distance =
      initial.lo + 2 + timestampBase * carry := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by have := pb.1; omega)
      (by
        have := ib.1
        rcases (show carry = 0 ∨ carry = 1 by omega) with rfl | rfl
        · simp only [mul_zero, add_zero]; omega
        · simp only [mul_one]; omega)
    exact lowCast
  have highNat : previous.hi + carry = initial.hi := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by have := pb.2; omega) (by have := ib.2; omega)
    exact highCast
  have highScaled := congrArg (fun x : Nat => timestampBase * x) highNat
  simp only [mul_add] at highScaled
  simp only [Timestamp.value]
  omega


theorem theta_rho_lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).length = 51 := by rfl

theorem chi5_lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (Chi5.importedConstraints (Chi5.setup (p := p)))).length = 18 := by rfl

/-- The theta/rho controller query (native generic lookup 9, after the alignment query). -/
noncomputable def thetaRhoControlQuery {p : Nat} [Fact p.Prime] : Lookup (ZMod p) :=
  (FlatOperation.lookups (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))).get
    ⟨10, by rw [theta_rho_lookup_count]; omega⟩

theorem theta_rho_control_arity {p : Nat} [Fact p.Prime] :
    (thetaRhoControlQuery (p := p)).table.arity = 9 := by rfl

theorem theta_rho_control_shape {p : Nat} [Fact p.Prime] :
    thetaRhoControlQuery (p := p) = Lookup.mk (ThetaRho.setup (p := p)).toRaw
      ((thetaRhoControlQuery (p := p)).entry.cast theta_rho_control_arity) := by rfl

/-- The chi5 controller query (native generic lookup 0, after the alignment query). -/
noncomputable def chi5ControlQuery {p : Nat} [Fact p.Prime] : Lookup (ZMod p) :=
  (FlatOperation.lookups (Chi5.importedConstraints (Chi5.setup (p := p)))).get
    ⟨1, by rw [chi5_lookup_count]; omega⟩

theorem chi5_control_arity {p : Nat} [Fact p.Prime] :
    (chi5ControlQuery (p := p)).table.arity = 11 := by rfl

theorem chi5_control_shape {p : Nat} [Fact p.Prime] :
    chi5ControlQuery (p := p) = Lookup.mk (Chi5.setup (p := p)).toRaw
      ((chi5ControlQuery (p := p)).entry.cast chi5_control_arity) := by rfl

theorem getElem_cast_map {α β : Type} [Inhabited α] {n m : Nat} (h : n = m)
    (v : Vector α n) (f : α → β) (i : Nat) (hi : i < m) :
    ((v.cast h).map f)[i] = f (v.toArray[i]!) := by
  subst h
  have hv : i < v.toArray.size := by simpa using hi
  simp [getElem!_pos v.toArray i hv]

theorem theta_rho_control_entries {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    let row := ((thetaRhoControlQuery (p := p)).entry.cast theta_rho_control_arity).map
      (Expression.eval (Verification.environment w))
    row[8] = 59 ∧ row[1] = w 0 ∧ ∀ index : Fin 5, row[3 + index.val] = w (84 + index.val) := by
  intro row
  refine ⟨?_, ?_, ?_⟩
  · simp only [row]; rw [getElem_cast_map]
    simp [thetaRhoControlQuery, ThetaRho.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  · simp only [row]; rw [getElem_cast_map]
    simp [thetaRhoControlQuery, ThetaRho.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]
  · intro index
    simp only [row]; rw [getElem_cast_map]
    fin_cases index <;>
      simp [thetaRhoControlQuery, ThetaRho.importedConstraints, FlatOperation.lookups,
        Expression.eval, Verification.environment]

theorem chi5_control_entries {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    let row := ((chi5ControlQuery (p := p)).entry.cast chi5_control_arity).map
      (Expression.eval (Verification.environment w))
    row[10] = 66 ∧ row[1] = w 0 ∧ row[8] = w 54 := by
  intro row
  refine ⟨?_, ?_, ?_⟩ <;> simp only [row] <;> rw [getElem_cast_map] <;>
    simp [chi5ControlQuery, Chi5.importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment]

/-- The theta/rho controller lookup yields exactly one live iteration flag for
an active row, in the witness columns used by the grouped distance equations. -/
theorem theta_rho_control_selector [Fact p.Prime]
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints (ThetaRho.setup (p := p)))) (active : w 0 = 1) :
    ∃ selected : Fin 5, ∀ index : Fin 5,
      w (84 + index.val) = if index = selected then 1 else 0 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (ThetaRho.importedConstraints (ThetaRho.setup (p := p)))
      ThetaRho.importedConstraintsTimestampLookups)
  have lookup : (thetaRhoControlQuery (p := p)).Contains (Verification.environment w) :=
    Verification.lookup_of_holds core _
  rw [theta_rho_control_shape] at lookup
  have sound : (ThetaRho.setup (p := p)).toRaw.Soundness #[] _ :=
    (ThetaRho.setup (p := p)).toRaw.imply_soundness _ _ lookup
  obtain ⟨tag, enabled, flags⟩ := theta_rho_control_entries w
  obtain ⟨selected, chosen⟩ := control.thetaRho _ sound tag (enabled.trans active)
  refine ⟨selected, fun index => ?_⟩
  rw [← flags index]
  exact chosen index

/-- The fixed chi5 controller row bounds the row index used in all six grouped distances. -/
theorem chi5_control_row_bound [Fact p.Prime]
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints (Chi5.setup (p := p)))) (active : w 0 = 1) :
    (w 54).val < 5 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (Chi5.importedConstraints (Chi5.setup (p := p)))
      Chi5.importedConstraintsTimestampLookups)
  have lookup : (chi5ControlQuery (p := p)).Contains (Verification.environment w) :=
    Verification.lookup_of_holds core _
  rw [chi5_control_shape] at lookup
  have sound : (Chi5.setup (p := p)).toRaw.Soundness #[] _ :=
    (Chi5.setup (p := p)).toRaw.imply_soundness _ _ lookup
  obtain ⟨tag, enabled, index⟩ := chi5_control_entries w
  rw [← index]
  exact control.chi5 _ sound tag (enabled.trans active)

/-- Every active theta/rho grouped distance is one of the source constants
1, 2, 3, 4, 5 or 6. The one-hot fact comes from the fixed controller table. -/
theorem theta_rho_distance_nat [Fact p.Prime]
    (hp : 6 < p)
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
    (_hp : 10 < p)
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
    (hp : 2 * Trace.timestampBase + 4 < p)
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints (ThetaRho.setup (p := p)))) (active : w 0 = 1)
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
    (by norm_num [Trace.timestampBase] at hp; omega) active
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


theorem chi5_group_order [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints (Chi5.setup (p := p)))) (active : w 0 = 1)
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
    (by norm_num [Trace.timestampBase] at hp; omega) active
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

/-- Every physical theta/rho port has the previous timestamp of one checked
native group. This is a finite, kernel-checked fact about imported metadata. -/
theorem theta_rho_port_group (i : Fin 16) :
    ∃ j : Fin 4,
      (ThetaRho.importedConstraintsMemoryPorts[i]).clock.previous =
        ThetaRho.importedConstraintsTimestampGroups[j].previous := by
  fin_cases i <;> decide +kernel

theorem chi5_port_group (i : Fin 12) :
    ∃ j : Fin 6,
      (Chi5.importedConstraintsMemoryPorts[i]).clock.previous =
        Chi5.importedConstraintsTimestampGroups[j].previous := by
  fin_cases i <;> decide +kernel

/-- The actual theta/rho port reads before its native write. The
bounded previous clock is supplied by exact logical memory matching. -/
theorem theta_rho_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints (ThetaRho.setup (p := p)))) (active : w 0 = 1)
    (i : Fin 16)
    (initial : (Trace.decodeTimestamp w
      ThetaRho.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      (ThetaRho.importedConstraintsMemoryPorts[i]).clock.previous).Bounded) :
    (Trace.decodeTimestamp w
      (ThetaRho.importedConstraintsMemoryPorts[i]).clock.previous).value <
      (Trace.decodeTimestamp w
        ThetaRho.importedConstraintsDelegationColumns.invocation).value +
        (ThetaRho.importedConstraintsMemoryPorts[i]).clock.offset := by
  obtain ⟨j, hj⟩ := theta_rho_port_group i
  have offset : (ThetaRho.importedConstraintsMemoryPorts[i]).clock.offset = 2 := by
    fin_cases i <;> decide +kernel
  rw [hj] at previous ⊢
  rw [offset]
  exact theta_rho_group_order hp control h active j initial previous

/-- Every physical chi5 port reads before its native write. -/
theorem chi5_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints (Chi5.setup (p := p)))) (active : w 0 = 1)
    (i : Fin 12)
    (initial : (Trace.decodeTimestamp w
      Chi5.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      (Chi5.importedConstraintsMemoryPorts[i]).clock.previous).Bounded) :
    (Trace.decodeTimestamp w
      (Chi5.importedConstraintsMemoryPorts[i]).clock.previous).value <
      (Trace.decodeTimestamp w
        Chi5.importedConstraintsDelegationColumns.invocation).value +
        (Chi5.importedConstraintsMemoryPorts[i]).clock.offset := by
  obtain ⟨j, hj⟩ := chi5_port_group i
  have offset : (Chi5.importedConstraintsMemoryPorts[i]).clock.offset = 2 := by
    fin_cases i <;> decide +kernel
  rw [hj] at previous ⊢
  rw [offset]
  exact chi5_group_order hp control h active j initial previous

/-- The indexed theta/rho theorem applies to any native port selected from
the imported physical port array. -/
theorem theta_rho_member_port_order {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints (ThetaRho.setup (p := p)))) (active : w 0 = 1)
    {port : Trace.MemoryPort}
    (member : port ∈ ThetaRho.importedConstraintsMemoryPorts)
    (initial : (Trace.decodeTimestamp w
      ThetaRho.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w port.clock.previous).Bounded) :
    (Trace.decodeTimestamp w port.clock.previous).value <
      (Trace.decodeTimestamp w
        ThetaRho.importedConstraintsDelegationColumns.invocation).value +
        port.clock.offset := by
  obtain ⟨i, bound, same⟩ := Array.mem_iff_getElem.mp member
  let index : Fin 16 := ⟨i, by simpa [theta_rho_memory_ports] using bound⟩
  subst port
  simpa [index] using theta_rho_physical_port_order hp control h active
    index initial previous


/-- Every native chi5 physical port reads before its write. -/
theorem chi5_member_port_order {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p)
    (control : ControlFacts p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints (Chi5.setup (p := p)))) (active : w 0 = 1)
    {port : Trace.MemoryPort}
    (member : port ∈ Chi5.importedConstraintsMemoryPorts)
    (initial : (Trace.decodeTimestamp w
      Chi5.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w port.clock.previous).Bounded) :
    (Trace.decodeTimestamp w port.clock.previous).value <
      (Trace.decodeTimestamp w
        Chi5.importedConstraintsDelegationColumns.invocation).value +
        port.clock.offset := by
  obtain ⟨i, bound, same⟩ := Array.mem_iff_getElem.mp member
  let index : Fin 12 := ⟨i, by simpa [chi5_memory_ports] using bound⟩
  subst port
  simpa [index] using chi5_physical_port_order hp control h active
    index initial previous

/-- Every split worker's imported constraints and port metadata give strict
    read-before-write clock order. -/
theorem split_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (control : ControlFacts p) (row : Native.Row p)
    (h : FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) row.constraints)
    (active : row.assignment row.columns.execute = 1)
    {port : Trace.MemoryPort} (member : port ∈ row.ports)
    (initial : (Trace.decodeTimestamp row.assignment row.columns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp row.assignment port.clock.previous).Bounded)
    (room : (Trace.decodeTimestamp row.assignment row.columns.invocation).lo + port.clock.offset <
      Trace.timestampBase) :
    (Trace.decodeTimestamp row.assignment port.clock.previous).value <
      (Trace.decodeTimestamp row.assignment row.columns.invocation).value + port.clock.offset := by
  have clockMember : port.clock ∈ row.columns.ports := by
    rw [← split_port_clocks_match row]
    exact Array.mem_map_of_mem member
  cases row with
  | mk kind w =>
    cases kind
    · exact column_parity_port_order hp h clockMember initial previous room
    · exact theta_rho_member_port_order hp control h active member initial previous
    · exact chi5_member_port_order hp control h active member initial previous

end Airbender.Keccak.Split.Proofs
