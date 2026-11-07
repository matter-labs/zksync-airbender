import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Trace.Workers.Keccak.Call
import Airbender.Review.Circuits.Keccak.Memory
import Airbender.Review.Trace.Workers.Keccak.BoundaryCall
import Airbender.Proofs.Delegation.BoundaryInputs
import Airbender.Proofs.Delegation.Readonly

namespace Airbender.Keccak.Proofs
open Trace Reference.RiscV.Sail

structure BoundaryCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : State) (cells : List Cell) : Prop where
  memory : Delegation.Proofs.BoundaryInputs data initial cells
  controlCell : Cell.register 10 ∈ cells
  controlStart : (Cell.register 10).read initial = .ok 0 initial
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  calls : data.rows.length = 649

structure BoundaryMemoryInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : State) (cells : List Cell) (control : Fin 4096 → Vector Nat 6) : Prop where
  publicState : Delegation.Proofs.BoundaryInputs data initial cells
  families : ∀ row ∈ data.rows, row.family = .keccak
  table : data.setup.keccak = setupTable control
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1

end Airbender.Keccak.Proofs

namespace Airbender.Keccak

def CallInputs.toBoundaryInputs [Fact p.Prime] {data : Delegation.MemoryData p}
    {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (inputs : CallInputs data initial cells) : Proofs.BoundaryCallInputs data initial cells :=
  ⟨inputs.memory.toBoundaryInputs, inputs.controlCell, inputs.controlStart, inputs.family,
    inputs.active, inputs.calls⟩

def Memory.Inputs.toBoundaryInputs [Fact p.Prime] {data : Delegation.MemoryData p}
    {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6}
    (inputs : Memory.Inputs data initial cells control) : Proofs.BoundaryMemoryInputs data initial cells control :=
  ⟨inputs.publicState.toBoundaryInputs, inputs.families, inputs.table, inputs.active⟩

def NativeCallInputs.toBoundaryInputs [Fact p.Prime] {data : Delegation.MemoryData p}
    {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (inputs : NativeCallInputs data initial cells) (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (accepted : Delegation.MemoryAccepted data) : Proofs.BoundaryCallInputs data initial cells := by
  have memory := inputs.memory.toBoundaryInputs
  have nonempty : data.rows ≠ [] := by
    intro empty
    have count := inputs.calls
    simp [empty] at count
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have family := inputs.family row member
  have port : importedConstraintsMemoryPorts[0] ∈ row.ports := by
    simp [Delegation.Row.ports, family, importedConstraintsMemoryPorts]
  have tracked := Delegation.Proofs.port_initialized_cell hp accepted memory member port
    (cell := .register 10) (by rfl)
  exact ⟨memory, tracked, inputs.controlStart, inputs.family, inputs.active, inputs.calls⟩

end Airbender.Keccak
