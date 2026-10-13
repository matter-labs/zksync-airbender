import Airbender.Review.Helpers.Delegation.Operations
import Airbender.Proofs.Bigint.Memory
import Airbender.Proofs.Blake2G.Memory
import Airbender.Proofs.Blake2Round.Memory
import Airbender.Proofs.Keccak.Memory

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true

theorem operation_rules_of_queries [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {control : Fin 4096 → Vector Nat 6}
    (constraints : ∀ row ∈ data.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.setup))
    (tables : data.setup = modeledSetup control)
    (rounds : ∀ row ∈ data.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round)
    (keccakActive : ∀ row ∈ data.rows, row.family = .keccak → row.assignment Keccak.Variables.execute = 1) :
    WriteBoundsFromReads data := by
  intro row member reads
  cases row with
  | mk family w =>
    have h := constraints ⟨family, w⟩ member
    cases family
    all_goals simp only [Row.constraints, tables, modeledSetup] at h
    · exact Bigint.Proofs.memory_write_rule (by omega) h reads
    · exact Blake2G.Proofs.memory_write_rule (by omega) inverse h reads
    · obtain ⟨round, mask⟩ := rounds ⟨.blakeRound, w⟩ member rfl
      exact Blake2Round.Proofs.memory_write_rule hp inverse h round mask reads
    · exact Keccak.Proofs.memory_write_rule (by omega) h
        (keccakActive ⟨.keccak, w⟩ member rfl) reads

theorem operation_rules [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells control) :
    WriteBoundsFromReads data :=
  operation_rules_of_queries hp inverse accepted.constraints inputs.tables inputs.rounds inputs.keccakActive

theorem operation_word_bounds_at_boundary [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : MemoryAccepted data) (inputs : BoundaryOperationInputs data before cells control) :
    WordBounds data := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have rules := operation_rules_of_queries hp inverse accepted.constraints inputs.tables inputs.rounds inputs.keccakActive
  exact ⟨fun _ member _ present => read_value_bounds size accepted inputs.publicState rules member present,
    fun _ member _ present => write_value_bounds size accepted inputs.publicState rules member present,
    fun _ present => terminal_value_bounds size accepted inputs.publicState rules present⟩

theorem operation_word_bounds [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells control) :
    WordBounds data :=
  operation_word_bounds_at_boundary hp inverse accepted inputs.toBoundaryInputs

end Airbender.Delegation.Proofs
