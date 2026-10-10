import Airbender.Review.Keccak.Iota
import Airbender.Review.Keccak.Controller
import Airbender.Review.Keccak.Addresses
import Airbender.Review.Delegation.Operations
import Airbender.Review.Delegation.Execution

namespace Airbender.Keccak.Native
open Trace

/-- One 64-bit lane observed through its two imported RV32 ports. Port numbers
    stay in these observations; shared history establishes their actual Sail
    read/write values and their bounds. -/
def readLane (w : Nat → ZMod p) (lane : Fin 6) : Nat :=
  let row : Delegation.Row p := ⟨.keccak, w⟩
  (row.readWord ⟨2 + 2 * lane.val, by change _ < 14; have := lane.isLt; omega⟩).value +
    2 ^ 32 * (row.readWord ⟨3 + 2 * lane.val, by change _ < 14; have := lane.isLt; omega⟩).value

def writtenLane (w : Nat → ZMod p) (lane : Fin 6) : Nat :=
  let row : Delegation.Row p := ⟨.keccak, w⟩
  (row.writtenWord ⟨2 + 2 * lane.val, by change _ < 14; have := lane.isLt; omega⟩).value +
    2 ^ 32 * (row.writtenWord ⟨3 + 2 * lane.val, by change _ < 14; have := lane.isLt; omega⟩).value

/-- The six actual writes, ordered as the native lane ports. -/
def writtenLanes (w : Nat → ZMod p) : Vector Nat 6 := Vector.ofFn (writtenLane w)

/-- Identify a reference column with the five actual native reads. This is
    an input interpretation inside the proved effects, not an external premise
    supplying reads to initialized memory history. -/
def ColumnReads (state : Vector Nat 25) (column : Fin 5) (w : Nat → ZMod p) : Prop :=
  ∀ lane : Fin 5, readLane w ⟨lane.val, by omega⟩ = state[5 * column.val + lane.val]

/-- Consequences for one actual Keccak row in initialized mixed delegation
    history. The controller selects physical lanes using the modeled Rust table;
    native addresses use its public, history-derived x11 pointer. Lane effects
    describe actual port writes using the existing Clean operation references.

    No read, pointer/operand range, expected write or selector is assumed.
    A complete request ABI and 24-round schedule remain separate obligations. -/
structure RowEffects (w : Nat → ZMod p) : Prop where
  iota : ∀ (state : Vector Nat 25) (column : Fin 5) (round : Fin 25),
    (w 3).val = (ControlState.mk 0 column ⟨round.val, by omega⟩).packed →
    ColumnReads state column w → IotaResult state column round w
  control : ControlUpdateChecks w
  indices : ∃ key : Fin 4096, key.val = (w 3).val + 2048 * (w 0).val ∧
    ∀ lane : Fin 6, (w (7 + lane.val)).val = (Controller.rows key)[lane]
  addresses : AddressChecks w
  theta : ∀ state : ControlState, (w 3).val = state.packed → state.mode = 3 →
    (∀ lane : Fin 5, writtenLane w ⟨lane.val, by omega⟩ =
      readLane w ⟨lane.val, by omega⟩ ^^^ readLane w 5) ∧
    writtenLane w 5 = readLane w 5

  rho : ∀ state : ControlState, (w 3).val = state.packed → state.mode = 4 →
    ∀ lane : Fin 5, writtenLane w ⟨lane.val, by omega⟩ =
      rotLeft64 (readLane w ⟨lane.val, by omega⟩) rhoRotations[state.iteration][lane]
  chiFirst : ∀ state : ControlState, (w 3).val = state.packed → state.mode = 5 →
    writtenLanes w = #v[
      readLane w 0 ^^^ ((not64 (readLane w 1)) &&& readLane w 2),
      readLane w 1 ^^^ ((not64 (readLane w 2)) &&& readLane w 3),
      readLane w 2, readLane w 3, (not64 (readLane w 0)) &&& readLane w 1, readLane w 0]
  chiSecond : ∀ state : ControlState, (w 3).val = state.packed → state.mode = 6 →
    writtenLanes w = #v[
      readLane w 0 ^^^ readLane w 3,
      readLane w 1 ^^^ ((not64 (readLane w 2)) &&& readLane w 0),
      readLane w 2 ^^^ ((not64 (readLane w 0)) &&& readLane w 4),
      readLane w 3, readLane w 4, readLane w 5]

end Airbender.Keccak.Native
