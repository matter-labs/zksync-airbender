module
public import Proven.Trace.Machine.UnrolledMemoryFacts
public import Proven.Trace.Machine.MemoryWorkerRules
public import Proven.Trace.Machine.UnrolledZeroRows
public import Proven.Trace.Machine.WorkerZero
public import Proven.Trace.TransferValues

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Public decoder metadata and native caller zeroes preserve x0 in the shared memory induction. -/
theorem unrolled_zero_rules {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {addresses : List (BitVec 32)}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (programImage : rvMachineProgramImage config initialState addresses = some program)
    : Transfer.CellWriteRules (unrolledMemory trace workers) (Cell.register 0).addressCode 0 := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  intro edge present address reads
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := Delegation.Caller.Proofs.machine_port_native row (by simpa using portMember)
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
        rw [current] at portMember
        have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨ port = AddSub.importedConstraintsMemoryPorts[2] := by
          simpa [Delegation.Caller.architecturalPorts] using portMember
        rcases modes with rfl | rfl
        · exact reads _ present (Nat.le_refl _) address
        · have holds := accepted.constraints _ member
          have core := Verification.holds_of_sublist holds
            (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
          have zero := AddSub.Proofs.delegation_zeroes (w := w) core mode
          simp [Trace.Row.columns, CircuitLayout.columns, writeToken,
            MemoryPort.writeCode, WordColumns.code, AddSub.importedConstraintsMemoryPorts,
            zero.2.2.2.2.1, zero.2.2.2.2.2]
          rfl
    · obtain ⟨entry, included, family, query⟩ := accepted.decoded row member
      obtain ⟨_, _, instruction, _, fields⟩ := machine_entry_fetch programImage entry included
      have rules := unrolled_noncaller_zero unrolled (accepted.constraints row member) fields family query selected
      have current : Delegation.Caller.machinePorts row = row.ports := by
        unfold Delegation.Caller.machinePorts
        exact ite_eq_right selected
      have clock := clocks row member
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
