module
public import Human.Circuits.Bigint.Memory
public import Human.Helpers.Delegation.RVMemory

@[expose] public section

/-! Public inputs of the bigint memory model: the starting point is an `RV.State` (`Delegation.RVMemoryInputs`,
    cells read by `Cell.readRV`). RAM cells are RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW
    `ROM_END` (`RV.State.delegationRAM`); no pointer is required to be at or above `ROM_END`. The circuit model and its
    mapping are `Memory.circuitModel`. -/

namespace Airbender.Bigint.Memory

/-- An initialized pool of bigint rows from a public `RV.State`. RAM
    cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`. -/
structure RVInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (before : RV.State) (cells : List Trace.Cell) : Prop where
  publicState : Delegation.RVMemoryInputs data before cells
  families : ∀ row ∈ data.rows, row.family = .bigint
  table : data.setup.bigint = setupTable

/-- Interface assumptions of the bigint memory model: exactly `RVInputs`; the address, output and witness
    arguments are unused. -/
abbrev RVInterfaceAssumptions [Fact p.Prime] (data : Delegation.MemoryData p)
    (before : RV.State) (cells : List Trace.Cell)
    (_input : Addresses.Input) (_output : Addresses.Output) (_w : Nat → ZMod p) : Prop :=
  RVInputs data before cells

end Airbender.Bigint.Memory
