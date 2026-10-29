import Airbender.Proofs.Keccak.SplitControlLookup
import Airbender.Proofs.Keccak.SplitColumnParityClock
import Airbender.Proofs.Keccak.SplitArtifactChecks

namespace Airbender.Keccak.Split.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- Every physical theta/rho port has the previous timestamp of one checked
native group. This is a finite, kernel-checked fact about imported metadata. -/
theorem theta_rho_port_group (i : Fin 16) :
    ∃ j : Fin 4,
      (ThetaRho.importedConstraintsMemoryPorts[i]).clock.previous =
        ThetaRho.importedConstraintsTimestampGroups[j].previous := by
  fin_cases i <;> decide +kernel

theorem theta_rho_cached_port_group (i : Fin 16) :
    ∃ j : Fin 4,
      (ThetaRhoCached.importedConstraintsMemoryPorts[i]).clock.previous =
        ThetaRhoCached.importedConstraintsTimestampGroups[j].previous := by
  fin_cases i <;> decide +kernel

theorem chi5_port_group (i : Fin 12) :
    ∃ j : Fin 6,
      (Chi5.importedConstraintsMemoryPorts[i]).clock.previous =
        Chi5.importedConstraintsTimestampGroups[j].previous := by
  fin_cases i <;> decide +kernel

theorem chi5_cached_port_group (i : Fin 12) :
    ∃ j : Fin 6,
      (Chi5Cached.importedConstraintsMemoryPorts[i]).clock.previous =
        Chi5Cached.importedConstraintsTimestampGroups[j].previous := by
  fin_cases i <;> decide +kernel

/-- The actual uncached theta/rho port reads before its native write. The
bounded previous clock is supplied by exact logical memory matching. -/
theorem theta_rho_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup.thetaRho)) (active : w 0 = 1)
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

/-- Every physical cached theta/rho port reads before its native write. -/
theorem theta_rho_cached_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup.thetaRho)) (active : w 0 = 1)
    (i : Fin 16)
    (initial : (Trace.decodeTimestamp w
      ThetaRhoCached.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      (ThetaRhoCached.importedConstraintsMemoryPorts[i]).clock.previous).Bounded) :
    (Trace.decodeTimestamp w
      (ThetaRhoCached.importedConstraintsMemoryPorts[i]).clock.previous).value <
      (Trace.decodeTimestamp w
        ThetaRhoCached.importedConstraintsDelegationColumns.invocation).value +
        (ThetaRhoCached.importedConstraintsMemoryPorts[i]).clock.offset := by
  obtain ⟨j, hj⟩ := theta_rho_cached_port_group i
  have offset : (ThetaRhoCached.importedConstraintsMemoryPorts[i]).clock.offset = 2 := by
    fin_cases i <;> decide +kernel
  rw [hj] at previous ⊢
  rw [offset]
  exact theta_rho_cached_group_order hp control h active j initial previous

/-- Every physical uncached chi5 port reads before its native write. -/
theorem chi5_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup.chi5)) (active : w 0 = 1)
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

/-- Every physical cached chi5 port reads before its native write. -/
theorem chi5_cached_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup.chi5)) (active : w 0 = 1)
    (i : Fin 12)
    (initial : (Trace.decodeTimestamp w
      Chi5Cached.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w
      (Chi5Cached.importedConstraintsMemoryPorts[i]).clock.previous).Bounded) :
    (Trace.decodeTimestamp w
      (Chi5Cached.importedConstraintsMemoryPorts[i]).clock.previous).value <
      (Trace.decodeTimestamp w
        Chi5Cached.importedConstraintsDelegationColumns.invocation).value +
        (Chi5Cached.importedConstraintsMemoryPorts[i]).clock.offset := by
  obtain ⟨j, hj⟩ := chi5_cached_port_group i
  have offset : (Chi5Cached.importedConstraintsMemoryPorts[i]).clock.offset = 2 := by
    fin_cases i <;> decide +kernel
  rw [hj] at previous ⊢
  rw [offset]
  exact chi5_cached_group_order hp control h active j initial previous

/-- The indexed theta/rho theorem applies to any native port selected from
the imported physical port array. -/
theorem theta_rho_member_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRho.clockConstraints setup.thetaRho)) (active : w 0 = 1)
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


/-- Every native cached theta/rho physical port reads before its write. -/
theorem theta_rho_cached_member_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (ThetaRhoCached.clockConstraints setup.thetaRho)) (active : w 0 = 1)
    {port : Trace.MemoryPort}
    (member : port ∈ ThetaRhoCached.importedConstraintsMemoryPorts)
    (initial : (Trace.decodeTimestamp w
      ThetaRhoCached.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w port.clock.previous).Bounded) :
    (Trace.decodeTimestamp w port.clock.previous).value <
      (Trace.decodeTimestamp w
        ThetaRhoCached.importedConstraintsDelegationColumns.invocation).value +
        port.clock.offset := by
  obtain ⟨i, bound, same⟩ := Array.mem_iff_getElem.mp member
  let index : Fin 16 := ⟨i, by simpa [theta_rho_cached_memory_ports] using bound⟩
  subst port
  simpa [index] using theta_rho_cached_physical_port_order hp control h active
    index initial previous

/-- Every native uncached chi5 physical port reads before its write. -/
theorem chi5_member_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5.clockConstraints setup.chi5)) (active : w 0 = 1)
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

/-- Every native cached chi5 physical port reads before its write. -/
theorem chi5_cached_member_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Chi5Cached.clockConstraints setup.chi5)) (active : w 0 = 1)
    {port : Trace.MemoryPort}
    (member : port ∈ Chi5Cached.importedConstraintsMemoryPorts)
    (initial : (Trace.decodeTimestamp w
      Chi5Cached.importedConstraintsDelegationColumns.invocation).Bounded)
    (previous : (Trace.decodeTimestamp w port.clock.previous).Bounded) :
    (Trace.decodeTimestamp w port.clock.previous).value <
      (Trace.decodeTimestamp w
        Chi5Cached.importedConstraintsDelegationColumns.invocation).value +
        port.clock.offset := by
  obtain ⟨i, bound, same⟩ := Array.mem_iff_getElem.mp member
  let index : Fin 12 := ⟨i, by simpa [chi5_cached_memory_ports] using bound⟩
  subst port
  simpa [index] using chi5_cached_physical_port_order hp control h active
    index initial previous

/-- All six native capture families use their own imported constraints and
physical port metadata to establish strict read-before-write clock order. -/
theorem split_physical_port_order {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {setup : Native.Setup p} (control : Native.ControlSetupFacts setup)
    (cached : Bool) (row : Native.Row p)
    (h : FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) (row.constraints cached setup))
    (active : row.assignment (row.columns cached).execute = 1)
    {port : Trace.MemoryPort} (member : port ∈ row.ports cached)
    (initial : (Trace.decodeTimestamp row.assignment
      (row.columns cached).invocation).Bounded)
    (previous : (Trace.decodeTimestamp row.assignment port.clock.previous).Bounded)
    (room : (Trace.decodeTimestamp row.assignment
      (row.columns cached).invocation).lo + port.clock.offset <
      Trace.timestampBase) :
    (Trace.decodeTimestamp row.assignment port.clock.previous).value <
      (Trace.decodeTimestamp row.assignment
        (row.columns cached).invocation).value + port.clock.offset := by
  have clockMember : port.clock ∈ (row.columns cached).ports := by
    rw [← split_port_clocks_match cached row]
    exact Array.mem_map_of_mem member
  cases row with
  | mk kind w =>
    cases cached <;> cases kind
    · exact column_parity_port_order hp h clockMember initial previous room
    · exact theta_rho_member_port_order hp control h active member initial previous
    · exact chi5_member_port_order hp control h active member initial previous
    · exact column_parity_cached_port_order hp h clockMember initial previous room
    · exact theta_rho_cached_member_port_order hp control h active member initial previous
    · exact chi5_cached_member_port_order hp control h active member initial previous

end Airbender.Keccak.Split.Proofs
