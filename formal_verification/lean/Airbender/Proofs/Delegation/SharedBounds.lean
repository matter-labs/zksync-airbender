import Airbender.Review.Trace.Delegation.SharedOperations
import Airbender.Proofs.Delegation.SharedMemory
import Airbender.Proofs.Delegation.Operations
import Airbender.Proofs.Trace.TransferBounds

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

private theorem worker_rules [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedOperationInputs data before addresses cells) :
    Delegation.Proofs.WriteBoundsFromReads data.workers := by
  apply Delegation.Proofs.operation_rules_of_queries hp inverse accepted.workerConstraints inputs.tables inputs.rounds
  intro row member family
  have active := accepted.workerActive row member
  rw [Delegation.Row.columns, family] at active
  change row.assignment 0 = 1 at active ⊢
  exact active

theorem shared_write_rules [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedOperationInputs data before addresses cells)
    (requests : RequestBinding data before) : Transfer.WriteRules (sharedData data) := by
  intro edge edgeMember reads
  rcases List.mem_append.mp edgeMember with machine | worker
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have caller : row ∈ data.callers := accepted.callerRows.symm ▸ rowMember
    have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
        port = AddSub.importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using portMember
    rcases modes with rfl | rfl
    · exact reads _ edgeMember (Nat.le_refl _)
    · have zero := (requests.callers row caller).1.zeroDestination
      change (destination row.assignment).Bounded
      rw [zero]
      norm_num [Word.Bounded, limbBase]
  · obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    apply worker_rules hp inverse accepted inputs row rowMember ?_ port (by simpa using portMember)
    intro source sourceMember
    have included : (readToken row.assignment source, row.writeToken source) ∈ (sharedData data).steps :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨row, rowMember,
        List.mem_map.mpr ⟨source, by simpa using sourceMember, rfl⟩⟩))
    apply reads _ included
    have same : (row.writeToken source).time = (row.writeToken port).time := by
      simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset row sourceMember,
        Delegation.Proofs.port_offset row (by simpa using portMember)]
    rw [same]

theorem shared_word_bounds [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : SharedMemoryAccepted data) (inputs : SharedOperationInputs data before addresses cells)
    (requests : RequestBinding data before) : SharedWordBounds data := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have facts := shared_memory_facts size clockInverse accepted inputs.toSharedMemoryInputs requests
  have initialized := sharedInputs inputs.toSharedMemoryInputs
  have rules := shared_write_rules hp rotationInverse accepted inputs requests
  refine ⟨?_, Transfer.terminal_bounds facts initialized rules⟩
  intro edge present
  exact ⟨Transfer.read_bounds facts initialized rules edge present,
    Transfer.produced_bounds facts initialized rules edge.2
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩)))⟩

end Airbender.Delegation.Caller.Proofs
