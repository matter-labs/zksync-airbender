import Airbender.Review.Delegation.Memory
import Airbender.Review.Blake2G.Control

namespace Airbender.Blake2G.Memory

/-- Public conditions for a pool of G calls. Actual Sail initialization and
    native matching supply the words; caller-clock alignment remains explicit.
    The family/table fields select the imported G circuit and current modeled
    controller. There are no operand, pointer or previous-clock range premises. -/
structure InterfaceAssumptions [Fact p.Prime] (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell)
    (_input : Input) (_output : Words) (_w : Nat → ZMod p) : Prop where
  accepted : Delegation.MemoryAccepted data
  publicState : Delegation.MemoryInputs data before cells
  families : ∀ row ∈ data.rows, row.family = .blakeG
  table : data.setup.blakeG = setupTable Control.controllerRows

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
