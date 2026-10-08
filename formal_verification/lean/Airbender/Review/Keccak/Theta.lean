import Airbender.Review.Keccak.Tables

namespace Airbender.Keccak

/-- Four sixteen-bit limbs from two consecutive imported word ports. -/
def laneValue {p : Nat} (w : Nat → ZMod p) (start : Nat) : Nat :=
  (w start).val + 65536 * ((w (start + 1)).val +
    65536 * ((w (start + 4)).val + 65536 * (w (start + 5)).val))

abbrev readLane {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) :=
  laneValue w (15 + 8 * lane.val)

abbrev writeLane {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) :=
  laneValue w (17 + 8 * lane.val)

/-- Memory reads supply five state lanes and the shared D lane for one column.
    Controller-to-column selection and global memory transport are still external. -/
structure ThetaInterface {p : Nat} (state : Vector Nat 25) (d : Vector Nat 5)
    (column : Fin 5) (w : Nat → ZMod p) : Prop where
  active : w Variables.execute = 1
  thetaSelected : w Variables.modeColumns[(3 : Fin 7)] = 1
  stateReads : ∀ i : Fin 5, readLane w ⟨i.val, by omega⟩ = state[5 * column.val + i.val]
  dRead : readLane w 5 = d[column]

/-- The five actual writes match the selected column of Clean's original Theta
    update; the sixth scratch lane is preserved. Other columns are not covered. -/
def ThetaResult {p : Nat} (state : Vector Nat 25) (d : Vector Nat 5)
    (column : Fin 5) (w : Nat → ZMod p) : Prop :=
  (∀ i : Fin 5, writeLane w ⟨i.val, by omega⟩ =
    (Specs.Keccak256.thetaXor state d)[5 * column.val + i.val]) ∧
    writeLane w 5 = readLane w 5

end Airbender.Keccak
