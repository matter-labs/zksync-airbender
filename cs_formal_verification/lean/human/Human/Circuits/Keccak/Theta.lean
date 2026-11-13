module
public import Human.Circuits.Keccak.Tables.Setup

@[expose] public section

namespace Airbender.Keccak

/-- Four sixteen-bit limbs from two consecutive imported word ports. -/
def laneValue {p : Nat} (w : Nat → ZMod p) (start : Nat) : Nat :=
  (w start).val + 65536 * ((w (start + 1)).val +
    65536 * ((w (start + 4)).val + 65536 * (w (start + 5)).val))

abbrev writeLane {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) :=
  laneValue w (17 + 8 * lane.val)

end Airbender.Keccak
