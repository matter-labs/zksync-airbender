import Human.Circuits.Keccak.Theta
import Human.Circuits.Keccak.ControlUpdate

namespace Airbender.Keccak

/-- Airbender runs Iota before collecting the next round's column parities.
    Control round zero leaves the input unchanged; rounds 1–24 apply Clean's
    original Iota with constant 0–23. This names the reference state only. -/
def iotaState (state : Vector Nat 25) (round : Fin 25) : Vector Nat 25 :=
  if h : 0 < round.val then
    Specs.Keccak256.iota state Specs.Keccak256.roundConstants[round.val - 1]
  else state

/-- One native Iota call reads a five-lane column. The incoming x10 control
    selects mode zero, this column and a round in 0–24. These are input and
    memory mappings; no written value or operand bound is assumed.
    Global call scheduling and memory transport remain separate obligations. -/
structure IotaMapping {p : Nat} (state : Vector Nat 25) (column : Fin 5)
    (round : Fin 25) (w : Nat → ZMod p) : Prop where
  active : w Variables.execute = 1
  control : (w Variables.controlReadLo).val =
    (ControlState.mk 0 column ⟨round.val, by omega⟩).packed
  stateReads : ∀ i : Fin 5,
    readLane w ⟨i.val, by omega⟩ = state[5 * column.val + i.val]

/-- The native writes match the selected column after original Iota. Its
    sixth write is that column's parity from Clean's original Theta-C function.
    The scratch lane's previous value is irrelevant. -/
def IotaResult {p : Nat} (state : Vector Nat 25) (column : Fin 5)
    (round : Fin 25) (w : Nat → ZMod p) : Prop :=
  (∀ i : Fin 5, writeLane w ⟨i.val, by omega⟩ =
    (iotaState state round)[5 * column.val + i.val]) ∧
  writeLane w 5 = (Specs.Keccak256.thetaC (iotaState state round))[column]

end Airbender.Keccak
