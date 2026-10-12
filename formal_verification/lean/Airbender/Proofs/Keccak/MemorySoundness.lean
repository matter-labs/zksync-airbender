import Airbender.Review.Keccak.Memory
import Airbender.Proofs.Keccak.Memory
import Airbender.Proofs.Keccak.BoundaryInputs

namespace Airbender.Keccak.Memory.Proofs
open Trace
set_option warningAsError true

theorem memory_rules_at_boundary [Fact p.Prime] (hp : 1048576 ≤ p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Keccak.Proofs.BoundaryMemoryInputs data before cells control) :
    Delegation.Proofs.WriteBoundsFromReads data := by
  intro row member reads
  cases row with
  | mk family w =>
    have selected := inputs.families ⟨family, w⟩ member
    change family = .keccak at selected
    subst family
    have h := accepted.constraints ⟨.keccak, w⟩ member
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints data.setup.keccak) at h
    rw [inputs.table] at h
    exact Keccak.Proofs.memory_write_rule hp h (inputs.active _ member) reads

theorem value_bounds_at_boundary [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Keccak.Proofs.BoundaryMemoryInputs data before cells control) :
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) := by
  have size : 1048576 ≤ p := by norm_num [timestampBase] at hp; omega
  have rules := memory_rules_at_boundary size accepted inputs
  exact ⟨fun row member port present => Delegation.Proofs.read_value_bounds hp accepted
      inputs.publicState rules member present,
    fun row member port present => Delegation.Proofs.write_value_bounds hp accepted
      inputs.publicState rules member present,
    fun token present => Delegation.Proofs.terminal_value_bounds hp accepted inputs.publicState rules present⟩

theorem memory_rules [Fact p.Prime] (hp : 1048576 ≤ p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Inputs data before cells control) :
    Delegation.Proofs.WriteBoundsFromReads data :=
  memory_rules_at_boundary hp accepted inputs.toBoundaryInputs

theorem value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Inputs data before cells control) :
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) :=
  value_bounds_at_boundary hp accepted inputs.toBoundaryInputs

end Airbender.Keccak.Memory.Proofs
