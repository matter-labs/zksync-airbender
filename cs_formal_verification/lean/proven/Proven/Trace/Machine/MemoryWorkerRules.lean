module
public import Proven.Trace.Machine.MemoryWorkers

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Earlier bounded reads give bounded writes in the combined standard and split worker pool. -/
theorem worker_write_rules {workers : WorkerPools babyBearModulus}
    (accepted : WorkersAccepted workers)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows) :
    ∀ edge ∈ workers.steps,
      (∀ source ∈ workers.steps, (timeOfPair source.2.time).value ≤ (timeOfPair edge.2.time).value →
        source.1.word.Bounded) → edge.2.word.Bounded := by
  intro edge present earlier
  rcases List.mem_append.mp present with standard | split
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp standard
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native : port ∈ row.ports := by simpa using portMember
    apply standard_write_bounds accepted tables row member _ port native
    intro source sourceMember
    apply earlier (readToken row.assignment source, row.writeToken source)
      (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
        List.mem_map.mpr ⟨source, by simpa using sourceMember, rfl⟩⟩)))
    have same : (row.writeToken source).time = (row.writeToken port).time := by
      simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset row sourceMember,
        Delegation.Proofs.port_offset row native]
    rw [same]
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp split
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native : port ∈ row.ports := by simpa using portMember
    apply split_write_bounds accepted member _ port native
    intro source sourceMember
    apply earlier (readToken row.assignment source, row.writeToken source)
      (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, member,
        List.mem_map.mpr ⟨source, by simpa using sourceMember, rfl⟩⟩)))
    have same : (row.writeToken source).time = (row.writeToken port).time := by
      simp only [Keccak.Split.Native.Row.writeToken, Keccak.Split.Native.Proofs.port_offset row sourceMember,
        Keccak.Split.Native.Proofs.port_offset row native]
    rw [same]

end Airbender.Trace.Machine.Proofs
