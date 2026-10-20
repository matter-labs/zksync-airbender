import Human.Helpers.Delegation.Memory
import Human.Circuits.Bigint.Addresses

namespace Airbender.Bigint.Memory

/-- Public inputs for an initialized pool of bigint rows. Sail supplies the
    starting registers/RAM; native matching supplies later reads. The table is
    the current modeled setup. Caller-clock alignment remains in `publicState`
    until request binding is connected. This does not certify the caller ABI. -/
structure Inputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) : Prop where
  publicState : Delegation.MemoryInputs data before cells
  families : ∀ row ∈ data.rows, row.family = .bigint
  table : data.setup.bigint = setupTable

/-- The existing address mapping names x10/x11 and all sixteen indirect ports.
    Membership connects those same pointer words to initialized native history. -/
structure Mapping (data : Delegation.MemoryData p) (input : Addresses.Input)
    (output : Addresses.Output) (w : Nat → ZMod p) : Prop where
  words : Addresses.Mapping input output w
  member : (⟨.bigint, w⟩ : Delegation.Row p) ∈ data.rows

/-- Native bigint equations, lookup membership and logical memory matching.
    Pointer bounds are proved from this initialized history, not supplied per row. -/
def circuitModel [Fact p.Prime] (data : Delegation.MemoryData p) :
    Verification.CircuitModel Addresses.Input Addresses.Output (Nat → ZMod p) where
  satisfies := fun _ => Delegation.MemoryAccepted data
  represents := Mapping data

abbrev InterfaceAssumptions [Fact p.Prime] (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell)
    (_input : Addresses.Input) (_output : Addresses.Output) (_w : Nat → ZMod p) : Prop :=
  Inputs data before cells

end Airbender.Bigint.Memory
