module
public import Human.Circuits.Keccak.Tables.Setup
public import Human.Circuits.Keccak.Theta
public import Proven.Defs.Circuits.Keccak.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Keccak/Theta.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Keccak
abbrev readLane {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) :=
  laneValue w (15 + 8 * lane.val)
end Airbender.Keccak
