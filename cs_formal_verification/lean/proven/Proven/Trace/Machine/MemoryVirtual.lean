module
public import Proven.Trace.Machine.MemoryClocks
public import Proven.Delegation.CallerRequests
public import Proven.UnifiedReduced.Delegation

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The excluded unrolled CSR port has the native empty read clock for every selected caller CSR. -/
theorem unrolled_excluded_clock {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    {port : MemoryPort} (native : port ∈ row.ports)
    (excluded : port ∉ Delegation.Caller.machinePorts row) :
    (decodeTimestamp row.assignment port.clock.previous).Bounded := by
  by_cases selected : (row.family == .addSub && decide (Requests.Selected row.assignment)) = true
  · have family : row.family = .addSub := by cases equal : row.family <;> simp_all
    cases row with
    | mk kind w =>
      change kind = .addSub at family
      subst kind
      have mode : w 17 = 1 := by
        simpa [Requests.Selected, AddSub.importedConstraintsDecoderColumns] using selected
      have current : Delegation.Caller.machinePorts (⟨.addSub, w⟩ : Trace.Row babyBearModulus PooledFamily) =
          Delegation.Caller.architecturalPorts := by
        unfold Delegation.Caller.machinePorts
        exact ite_eq_left selected
      rw [current] at excluded
      have holds := accepted.constraints _ member
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have empty := AddSub.Proofs.delegation_zeroes (w := w) core mode
      simp [Trace.Row.ports, CircuitLayout.ports, AddSub.importedConstraintsMemoryPorts] at native
      rcases native with rfl | rfl | rfl
      · exact False.elim (excluded (by simp [Delegation.Caller.architecturalPorts, AddSub.importedConstraintsMemoryPorts]))
      · change (⟨(w 27).val, (w 28).val⟩ : Timestamp).Bounded
        rw [empty.2.2.1, empty.2.2.2.1]
        norm_num [Timestamp.Bounded, timestampBase]
      · exact False.elim (excluded (by simp [Delegation.Caller.architecturalPorts, AddSub.importedConstraintsMemoryPorts]))
  · have current : Delegation.Caller.machinePorts row = row.ports := by
      unfold Delegation.Caller.machinePorts
      exact ite_eq_right selected
    rw [current] at excluded
    exact False.elim (excluded native)

/-- The excluded unified CSR port has the same empty-clock contract for every selected caller CSR. -/
theorem unified_excluded_clock {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows)
    {port : MemoryPort} (native : port ∈ row.ports)
    (excluded : port ∉ UnifiedReduced.Caller.machinePorts row) :
    (decodeTimestamp row.assignment port.clock.previous).Bounded := by
  by_cases selected : UnifiedReduced.Caller.Selected row.assignment
  · cases row with
    | mk kind w =>
      cases kind
      have mode := selected
      change w 18 = 1 at mode
      have current : UnifiedReduced.Caller.machinePorts (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) =
          UnifiedReduced.Caller.architecturalPorts := by
        unfold UnifiedReduced.Caller.machinePorts
        exact ite_eq_left selected
      rw [current] at excluded
      have holds := accepted.constraints _ member
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom)
          UnifiedReduced.importedConstraintsTimestampLookups)
      have empty := UnifiedReduced.Caller.Proofs.caller_zeroes (w := w) core mode
      simp [Trace.Row.ports, CircuitLayout.ports, UnifiedReduced.importedConstraintsMemoryPorts] at native
      rcases native with rfl | rfl | rfl
      · exact False.elim (excluded (by simp [UnifiedReduced.Caller.architecturalPorts, UnifiedReduced.importedConstraintsMemoryPorts]))
      · change (⟨(w 40).val, (w 41).val⟩ : Timestamp).Bounded
        rw [empty.2.2.1, empty.2.2.2.1]
        norm_num [Timestamp.Bounded, timestampBase]
      · exact False.elim (excluded (by simp [UnifiedReduced.Caller.architecturalPorts, UnifiedReduced.importedConstraintsMemoryPorts]))
  · have current : UnifiedReduced.Caller.machinePorts row = row.ports := by
      unfold UnifiedReduced.Caller.machinePorts
      exact ite_eq_right selected
    rw [current] at excluded
    exact False.elim (excluded native)

end Airbender.Trace.Machine.Proofs
