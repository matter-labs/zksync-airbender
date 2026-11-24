module
public import Human.Trace.Machine.Model
public import Proven.Delegation.PortEvents
public import Proven.KeccakSplit.Memory.History

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true

/-- Every standard or split worker accesses RAM or a nonzero register. -/
theorem worker_not_zero {workers : WorkerPools p} {edge : MemoryToken p × MemoryToken p}
    (member : edge ∈ workers.steps) : edge.1.address ≠ (Cell.register 0).addressCode := by
  rcases List.mem_append.mp member with standard | split
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp standard
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact Delegation.Proofs.port_not_zero row (by simpa using present)
  · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp split
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    exact Keccak.Split.Native.Proofs.port_not_zero row (by simpa using present)

end Airbender.Trace.Machine.Proofs
