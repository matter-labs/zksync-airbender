module
public import Proven.Trace.Machine.UnifiedMemoryFacts
public import Proven.Trace.Machine.MemoryWorkerRules
public import Proven.Trace.Machine.UnifiedZeroRows
public import Proven.Trace.Machine.WorkerZero
public import Proven.Trace.TransferValues

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Public decoder metadata and native caller zeroes preserve x0 in unified shared memory. -/
theorem unified_zero_rules {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program) :
    Transfer.CellWriteRules (unifiedMemory trace workers) (Cell.register 0).addressCode 0 := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  intro edge present address reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := UnifiedReduced.Caller.Proofs.rv_machine_port_native row (by simpa using portMember)
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
        rw [current] at portMember
        have modes : port = UnifiedReduced.importedConstraintsMemoryPorts[0] ∨
            port = UnifiedReduced.importedConstraintsMemoryPorts[2] := by
          simpa [UnifiedReduced.Caller.architecturalPorts] using portMember
        rcases modes with rfl | rfl
        · exact reads _ present (Nat.le_refl _) address
        · have holds := accepted.constraints _ member
          have core := Verification.holds_of_sublist holds
            (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom)
              UnifiedReduced.importedConstraintsTimestampLookups)
          have zero := UnifiedReduced.Caller.Proofs.caller_zeroes (w := w) core mode
          simp [Trace.Row.columns, CircuitLayout.columns, writeToken,
            MemoryPort.writeCode, WordColumns.code, UnifiedReduced.importedConstraintsMemoryPorts,
            zero.2.2.2.2.1, zero.2.2.2.2.2]
          rfl
    · have current : UnifiedReduced.Caller.machinePorts row = row.ports := by
        unfold UnifiedReduced.Caller.machinePorts
        exact ite_eq_right selected
      have clock := clocks row member
      obtain ⟨entry, included, _, query⟩ := accepted.decoded row member
      obtain ⟨_, _, instruction, _, fields⟩ := machine_entry_fetch programImage entry included
      have rules := unified_noncaller_zero (accepted.constraints row member) (accepted.active row member) fields query selected
      apply rules port native address
      intro source sourceMember order same
      apply reads (readToken row.assignment source, writeToken row.columns row.assignment source)
        (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
          List.mem_map.mpr ⟨source, by simpa [current] using sourceMember, rfl⟩⟩)))
      · rw [native_row_write_time clock sourceMember, native_row_write_time clock native]
        exact order
      · exact same
  · exact False.elim (worker_not_zero worker address)

end Airbender.Trace.Machine.Proofs
