module
public import Proven.Trace.Machine.MemoryVirtual
public import Proven.Trace.Machine.MemoryWorkerOrder

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The accepted CPU and both worker pools form one strictly ordered architectural memory relation. -/
theorem unified_memory_facts {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {before : RV.State} {cells : List Cell}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV before cells = some trace.initialMemory) :
    Transfer.Facts (unifiedMemory trace workers) := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  have allClocks := shared_memory_clocks (data := unifiedMemory trace workers) accepted.memory
    (Transfer.rv_image_clocks image) (unified_write_clocks accepted initial aligned)
  refine ⟨accepted.memory, ?_, ?_⟩
  · intro edge member
    rcases List.mem_append.mp member with machine | worker
    · obtain ⟨_, _, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp step
      rfl
    · rcases List.mem_append.mp worker with standard | split
      · exact Delegation.Proofs.preserved_addresses edge standard
      · exact Keccak.Split.Native.Proofs.preserved_addresses edge split
  · intro edge present
    rcases List.mem_append.mp present with machine | worker
    · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
      have clock := clocks row member
      have allPrevious : ∀ timePort ∈ row.columns.ports,
          (decodeTimestamp row.assignment timePort.previous).Bounded := by
        intro timePort included
        rw [← ports_clocks row] at included
        obtain ⟨source, sourceMember, rfl⟩ := Array.mem_map.mp included
        by_cases architectural : source ∈ UnifiedReduced.Caller.machinePorts row
        · exact (allClocks _ (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
            List.mem_map.mpr ⟨source, by simpa using architectural, rfl⟩⟩)))).1
        · exact unified_excluded_clock accepted member sourceMember architectural
      have effects := ClockLaws.effects (by decide : 2 * timestampBase + 4 < babyBearModulus)
        (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1) trace.rom row
        (accepted.constraints row member) ⟨clock.1, clock.2, allPrevious⟩
      have native := UnifiedReduced.Caller.Proofs.rv_machine_port_native row (by simpa using portMember)
      have inClocks : port.clock ∈ row.columns.ports := by
        rw [← ports_clocks row]
        exact Array.mem_map.mpr ⟨port, native, rfl⟩
      exact (effects.accesses port.clock inClocks).1.trans_eq
        (write_time (by decide : timestampBase < babyBearModulus)
          (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2
          (Trace.Proofs.port_offset row port native)).2.symm
    · apply worker_memory_order accepted.toWorkersAccepted (unified_worker_clocks accepted initial aligned).1 _ edge worker
      intro source included
      exact (allClocks source (List.mem_append.mpr (Or.inr included))).1

end Airbender.Trace.Machine.Proofs
