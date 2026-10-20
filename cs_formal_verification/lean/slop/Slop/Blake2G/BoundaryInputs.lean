import Human.Trace.Workers.Blake2G.BoundaryCall
import Slop.Delegation.BoundaryInputs

namespace Airbender.Blake2G.Proofs
open Trace Reference.RiscV.Sail

structure BoundaryCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : State) (cells : List Cell) (reduced : Bool) : Prop where
  memory : Delegation.Proofs.BoundaryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlStart : (Cell.register 12).read initial =
    .ok (if reduced then 128 else 0) initial
  calls : data.rows.length = callCount reduced

end Airbender.Blake2G.Proofs

namespace Airbender.Blake2G

def CallInputs.toBoundaryInputs [Fact p.Prime] {data : Delegation.MemoryData p}
    {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {reduced : Bool}
    (inputs : CallInputs data initial cells reduced) : Proofs.BoundaryCallInputs data initial cells reduced :=
  ⟨inputs.memory.toBoundaryInputs, inputs.tables, inputs.family, inputs.active,
    inputs.controlStart, inputs.calls⟩

def NativeCallInputs.toBoundaryInputs [Fact p.Prime] {data : Delegation.MemoryData p}
    {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {reduced : Bool}
    (inputs : NativeCallInputs data initial cells reduced) : Proofs.BoundaryCallInputs data initial cells reduced :=
  ⟨inputs.memory.toBoundaryInputs, inputs.tables, inputs.family, inputs.active,
    inputs.controlStart, inputs.calls⟩

end Airbender.Blake2G
