import Human.Helpers.Delegation.Memory
import Human.Circuits.Bigint.Addresses

namespace Airbender.Bigint.Memory

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

end Airbender.Bigint.Memory
