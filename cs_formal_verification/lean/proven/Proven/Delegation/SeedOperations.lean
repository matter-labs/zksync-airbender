module
public import Proven.Delegation.Operations
public import Proven.Delegation.SeedMemory

@[expose] public section

/-! State-free twin of `Operations.operation_word_bounds_at_boundary`: the seed facts (`SeedInputs`) and the modeled
    operation tables bound every native read, write and terminal word. -/

namespace Airbender.Delegation.SeedProofs
open Trace
set_option warningAsError true

theorem operation_word_bounds [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {cells : List Cell} {control : Fin 4096 → Vector Nat 6}
    (accepted : MemoryAccepted data) (inputs : SeedInputs data cells)
    (tables : data.setup = modeledSetup control)
    (rounds : ∀ row ∈ data.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round)
    (keccakActive : ∀ row ∈ data.rows, row.family = .keccak → row.assignment Keccak.Variables.execute = 1) :
    WordBounds data := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have rules := Proofs.operation_rules_of_queries hp inverse accepted.constraints tables rounds keccakActive
  exact ⟨fun _ member _ present => read_value_bounds size accepted inputs rules member present,
    fun _ member _ present => write_value_bounds size accepted inputs rules member present,
    fun _ present => terminal_value_bounds size accepted inputs rules present⟩

end Airbender.Delegation.SeedProofs
