module
public import Human.Helpers.Delegation.Memory
public import Human.Circuits.Blake2Round.Row

@[expose] public section

namespace Airbender.Blake2Round.Memory

/-- Historical name for the shared exclusive caller round-mask condition. -/
abbrev RoundMask {p : Nat} (w : Nat → ZMod p) (round : Fin 10) : Prop :=
  Control.RoundMask w round

end Airbender.Blake2Round.Memory
