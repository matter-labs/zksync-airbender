import Airbender.Review.Blake2Round.BoundaryCall
import Airbender.Proofs.Delegation.BoundaryInputs

namespace Airbender.Blake2Round.Proofs
open Trace Reference.RiscV.Sail

structure BoundaryCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : State) (cells : List Cell) (flags : Fin 8) : Prop where
  memory : Delegation.Proofs.BoundaryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  controlStart : (Cell.register 12).read initial =
    .ok (BitVec.ofNat 32 ((8 + flags.val) * 65536)) initial
  calls : data.rows.length = if flags.val % 2 = 1 then 7 else 10

end Airbender.Blake2Round.Proofs

namespace Airbender.Blake2Round

def CallInputs.toBoundaryInputs [Fact p.Prime] {data : Delegation.MemoryData p}
    {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {flags : Fin 8}
    (inputs : CallInputs data initial cells flags) : Proofs.BoundaryCallInputs data initial cells flags :=
  ⟨inputs.memory.toBoundaryInputs, inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩

def NativeCallInputs.toBoundaryInputs [Fact p.Prime] {data : Delegation.MemoryData p}
    {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {flags : Fin 8}
    (inputs : NativeCallInputs data initial cells flags) : Proofs.BoundaryCallInputs data initial cells flags :=
  ⟨inputs.memory.toBoundaryInputs, inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩

end Airbender.Blake2Round
