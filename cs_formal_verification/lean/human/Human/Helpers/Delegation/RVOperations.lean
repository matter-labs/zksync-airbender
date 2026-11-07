import Human.Helpers.Delegation.Operations
import Human.Helpers.Delegation.RVMemory

namespace Airbender.Delegation

/-- RV sibling of `OperationInputs`: the public state is an `RV.State` (`RVMemoryInputs`, whose RAM cells include the
    shadow RAM below `ROM_END`); the modeled tables and the caller/padding rules are unchanged. -/
structure RVOperationInputs [Fact p.Prime] (data : MemoryData p)
    (before : RV.State) (cells : List Trace.Cell)
    (control : Fin 4096 → Vector Nat 6) : Prop where
  publicState : RVMemoryInputs data before cells
  tables : data.setup = modeledSetup control
  rounds : ∀ row ∈ data.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round
  keccakActive : ∀ row ∈ data.rows, row.family = .keccak →
    row.assignment Keccak.Variables.execute = 1

end Airbender.Delegation
