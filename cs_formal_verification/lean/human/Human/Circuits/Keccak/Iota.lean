module
public import Human.Circuits.Keccak.Theta
public import Human.Circuits.Keccak.ControlUpdate

@[expose] public section

namespace Airbender.Keccak

/-- Airbender runs Iota before collecting the next round's column parities.
    Control round zero leaves the input unchanged; rounds 1–24 apply Clean's
    original Iota with constant 0–23. This names the reference state only. -/
def iotaState (state : Vector Nat 25) (round : Fin 25) : Vector Nat 25 :=
  if h : 0 < round.val then
    Specs.Keccak256.iota state Specs.Keccak256.roundConstants[round.val - 1]
  else state

/-- The native writes match the selected column after original Iota. Its
    sixth write is that column's parity from Clean's original Theta-C function.
    The scratch lane's previous value is irrelevant. -/
def IotaResult {p : Nat} (state : Vector Nat 25) (column : Fin 5)
    (round : Fin 25) (w : Nat → ZMod p) : Prop :=
  (∀ i : Fin 5, writeLane w ⟨i.val, by omega⟩ =
    (iotaState state round)[5 * column.val + i.val]) ∧
  writeLane w 5 = (Specs.Keccak256.thetaC (iotaState state round))[column]

end Airbender.Keccak
