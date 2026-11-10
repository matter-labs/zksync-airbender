module
public import Human.Circuits.Blake2Round.Memory
public import Slop.Defs.Circuits.Blake2Round.Row

/-! Definitions no claim states, moved from `human/Human/Circuits/Blake2Round/Memory.lean`. -/

@[expose] public section

namespace Airbender.Blake2Round.Memory

/-- `Row.Mapping` names the actual controller, pointers, state/message reads
    and native writes. Membership binds that same assignment to the initialized
    history; `round` interprets its exclusive mask as the declared round. -/
structure Mapping (data : Delegation.MemoryData p) (input : Row.Input) (output : Row.Output)
    (w : Nat → ZMod p) : Prop where
  words : Row.Mapping input output w
  member : (⟨.blakeRound, w⟩ : Delegation.Row p) ∈ data.rows
  round : RoundMask w input.round

/-- All native equations, modeled XOR lookups and timestamp queries. The
    conclusion uses the existing project preparation and pinned Clean round. -/
def circuitModel [Fact p.Prime] (data : Delegation.MemoryData p) :
    Verification.CircuitModel Row.Input Row.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (clockConstraints setupTable)
  represents := Mapping data

end Airbender.Blake2Round.Memory
