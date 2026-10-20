import Human.Circuits.Keccak.Mix

namespace Airbender.Keccak.Proofs
set_option warningAsError true
theorem lane_of_limbs {p : Nat} {left right : Nat → ZMod p} {i : Fin 6}
    (same : readLaneLimbs right i = writeLaneLimbs left i) : readLane right i = writeLane left i := by
  have l0 := congrArg (fun v : Vector (ZMod p) 4 => v[0]) same
  have l1 := congrArg (fun v : Vector (ZMod p) 4 => v[1]) same
  have l2 := congrArg (fun v : Vector (ZMod p) 4 => v[2]) same
  have l3 := congrArg (fun v : Vector (ZMod p) 4 => v[3]) same
  simp only [readLaneLimbs, writeLaneLimbs, Vector.getElem_map] at l0 l1 l2 l3
  dsimp at l0 l1 l2 l3
  change right (15 + 8 * i.val) = left (17 + 8 * i.val) at l0
  change right (16 + 8 * i.val) = left (18 + 8 * i.val) at l1
  change right (19 + 8 * i.val) = left (21 + 8 * i.val) at l2
  change right (20 + 8 * i.val) = left (22 + 8 * i.val) at l3
  simp only [readLane, writeLane, laneValue]
  rw [show 15 + 8 * i.val + 1 = 16 + 8 * i.val by omega,
    show 15 + 8 * i.val + 4 = 19 + 8 * i.val by omega,
    show 15 + 8 * i.val + 5 = 20 + 8 * i.val by omega,
    show 17 + 8 * i.val + 1 = 18 + 8 * i.val by omega,
    show 17 + 8 * i.val + 4 = 21 + 8 * i.val by omega,
    show 17 + 8 * i.val + 5 = 22 + 8 * i.val by omega,
    l0, l1, l2, l3]

end Airbender.Keccak.Proofs
