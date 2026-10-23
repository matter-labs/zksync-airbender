import Airbender.Review.Circuits.Keccak.Rho

namespace Airbender.Keccak.Controller
set_option warningAsError true

/-- Source coordinate for Keccak Pi, in Clean's column-major lane order.
    The original `rhoPi` and `rhoDestinations` remain the operation reference. -/
def piSource (lane : Fin 25) : Fin 25 :=
  ⟨5 * ((lane.val / 5 + 3 * (lane.val % 5)) % 5) + lane.val / 5, by
    have := lane.isLt; have := Nat.mod_lt (lane.val / 5 + 3 * (lane.val % 5)) (by decide : 0 < 5)
    omega⟩

/-- Physical location of a logical lane before a round. The first layout is
    row-major; Rho writes in place, so Pi changes the logical-to-physical map.
    This recurrence replaces the 625-entry Rust permutation constant. -/
def physicalLane : Nat → Fin 25 → Nat
  | 0, lane => lane.val / 5 + 5 * (lane.val % 5)
  | round + 1, lane => physicalLane round (piSource lane)


end Airbender.Keccak.Controller
