import Airbender.Review.Circuits.Keccak.Controller

namespace Airbender.Keccak.Controller
set_option warningAsError true

/-- Modeled native controller rows from
    `cs/src/tables/keccak_precompile_related.rs`.

    Bit 11 marks an active call. Lower bits encode mode, iteration and round.
    The first five outputs select state lanes; the sixth may select parity or
    scratch. Mix and Chi also use scratch slots 25–30. Invalid controls retain
    Rust's fallback rows; this table does not enforce a complete call schedule.
    Setup-generator fidelity remains the existing modeled-table boundary. -/
def rows (key : Fin 4096) : Vector Nat 6 :=
  let mode := key.val % 8
  let iteration := key.val / 8 % 8
  let round := key.val / 64 % 32
  if iteration < 5 then
    let column := fun i : Fin 5 => physicalLane round (Fin.ofNat 25 (5 * iteration + i.val))
    if mode = 0 ∧ round ≤ 24 ∧ 2048 ≤ key.val then
      Vector.ofFn fun i : Fin 6 => if i.val < 5 then column (Fin.ofNat 5 i.val) else 25 + iteration
    else if (mode = 1 ∨ mode = 2) ∧ round < 24 then #v[25, 26, 27, 28, 29, 30]
    else if mode = 3 ∧ round < 24 then
      Vector.ofFn fun i : Fin 6 => if i.val < 5 then column (Fin.ofNat 5 i.val) else 25 + (iteration + 4) % 5
    else if mode = 4 ∧ round < 24 then
      Vector.ofFn fun i : Fin 6 => if i.val < 5 then column (Fin.ofNat 5 i.val) else 25
    else if mode = 5 ∧ round < 24 then
      Vector.ofFn fun i : Fin 6 => if i.val < 4 then
        physicalLane (round + 1) (Fin.ofNat 25 (5 * (i.val + 1) + iteration)) else 25 + (i.val - 4)
    else if mode = 6 ∧ round < 24 then
      Vector.ofFn fun i : Fin 6 => if i.val = 0 then physicalLane (round + 1) (Fin.ofNat 25 iteration)
        else if i.val = 1 then physicalLane (round + 1) (Fin.ofNat 25 (15 + iteration))
        else if i.val = 2 then physicalLane (round + 1) (Fin.ofNat 25 (20 + iteration))
        else 25 + (i.val - 3)
    else if mode = 0 ∧ iteration = 0 ∧ round = 0 then Vector.replicate 6 0
    else #v[0, 1, 2, 3, 4, 5]
  else #v[0, 1, 2, 3, 4, 5]

end Airbender.Keccak.Controller
