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

/-- Consequences for one actual Keccak row in initialized mixed delegation
    history. The controller selects physical lanes using the modeled Rust table;
    native addresses use its public, history-derived x11 pointer. The Theta
    clause describes actual port writes; its XOR relation is the column
    projection of Clean's original `thetaXor`.

    No read, pointer/operand range, expected write or selector is assumed.
    A complete request ABI and 24-round schedule remain separate obligations. -/
structure RowEffects (w : Nat → ZMod p) : Prop where
  control : ControlUpdateChecks w
  indices : ∃ key : Fin 4096, key.val = (w 3).val + 2048 * (w 0).val ∧
    ∀ lane : Fin 6, (w (7 + lane.val)).val = (Controller.rows key)[lane]
  addresses : AddressChecks w
  theta : ∀ state : ControlState, (w 3).val = state.packed → state.mode = 3 →
    (∀ lane : Fin 5, writtenLane w ⟨lane.val, by omega⟩ =
      readLane w ⟨lane.val, by omega⟩ ^^^ readLane w 5) ∧
    writtenLane w 5 = readLane w 5

end Airbender.Keccak.Native
