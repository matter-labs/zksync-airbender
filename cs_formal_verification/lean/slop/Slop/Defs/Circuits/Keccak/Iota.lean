module
public import Human.Circuits.Keccak.Theta
public import Human.Circuits.Keccak.ControlUpdate
public import Human.Circuits.Keccak.Iota
public import Slop.Defs.Circuits.Keccak.Theta

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Keccak/Iota.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Keccak
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
end Airbender.Keccak
