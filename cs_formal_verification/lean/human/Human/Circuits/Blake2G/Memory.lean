module
public import Human.Helpers.Delegation.Memory
public import Human.Circuits.Blake2G.Control

@[expose] public section

namespace Airbender.Blake2G.Memory

/-- The existing word mapping names the six reads and four writes. Membership
    ties those exact columns to an access in the accepted initialized history. -/
structure Mapping (data : Delegation.MemoryData p) (input : Input) (output : Words)
    (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  member : (⟨.blakeG, w⟩ : Delegation.Row p) ∈ data.rows

/-- The native G equations and clock queries, interpreted with Clean. The
    output property remains the original Clean G reference from `Model.lean`. -/
def circuitModel [Fact p.Prime] (data : Delegation.MemoryData p) :
    Verification.CircuitModel Input Words (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (clockConstraints (setupTable Control.controllerRows))
  represents := Mapping data

end Airbender.Blake2G.Memory
