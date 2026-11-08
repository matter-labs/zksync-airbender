import Human.Helpers.Delegation.WorkerProjection
import Slop.Delegation.RequestTrace
import Slop.Trace.TransferValues

namespace Airbender.Delegation.Caller.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem worker_addresses {data : MemoryData p} :
    ∀ edge ∈ data.steps, edge.1.address ≠ (Cell.register 0).addressCode ∧
      edge.2.address ≠ (Cell.register 0).addressCode := by
  intro edge member
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp member
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  have nonzero := Delegation.Proofs.port_not_zero row (by simpa using portMember)
  exact ⟨nonzero, nonzero⟩

theorem filtered_architectural_tokens {p : Nat}
    (machine workers : List (MemoryToken p × MemoryToken p))
    (callerAddresses : ∀ edge ∈ machine, edge.1.address = (Cell.register 0).addressCode ∧
      edge.2.address = (Cell.register 0).addressCode)
    (workerAddresses : ∀ edge ∈ workers, edge.1.address ≠ (Cell.register 0).addressCode ∧
      edge.2.address ≠ (Cell.register 0).addressCode) (written : Bool) :
    (((machine ++ workers).map fun edge => if written then edge.2 else edge.1).filter fun token =>
      token.address != (Cell.register 0).addressCode) =
    workers.map (fun edge => if written then edge.2 else edge.1) := by
  have removed :
      ((machine).map
        (fun edge => if written then edge.2 else edge.1)).filter
        (fun token => token.address != (Cell.register 0).addressCode) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro token member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
    cases written <;> simp [(callerAddresses edge present).1, (callerAddresses edge present).2]
  have kept :
      (workers.map (fun edge => if written then edge.2 else edge.1)).filter
        (fun token => token.address != (Cell.register 0).addressCode) =
      workers.map (fun edge => if written then edge.2 else edge.1) := by
    apply List.filter_eq_self.mpr
    intro token member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
    cases written with
    | false => simpa only [Bool.false_eq_true, ite_false, bne_iff_ne] using (workerAddresses edge present).1
    | true => simpa only [ite_true, bne_iff_ne] using (workerAddresses edge present).2
  simp only [List.map_append, List.filter_append, removed, kept, List.nil_append]

end Airbender.Delegation.Caller.Proofs
