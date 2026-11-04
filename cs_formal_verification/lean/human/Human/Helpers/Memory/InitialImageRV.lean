import Human.Helpers.Memory.Values
import Human.Helpers.Context.PCState.Model
import Human.ISA.State

/-! RV-typed siblings of `InitialImage.lean`: the same public cell domain and
    seed tokens, but the starting point is an `RV.State`, not a Sail state.
    The `readable` failure of byte reads is kept (it is the RV memory map's
    range condition, `RV.readable`), so a cell outside the map still makes the
    construction fail. -/

namespace Airbender.Trace
open Arithmetic

/-- Read one public cell from an RV state. Registers read `getReg` (x0 is 0).
    RAM reads 4 bytes and fails outside the readable range, as `RV.readable`
    states. -/
def Cell.readRV (cell : Cell) (before : RV.State) : Option (BitVec 32) :=
  match cell with
  | .register index => some (before.getReg index)
  | .ram address =>
    if RV.readable address 4 then some (RV.read before.mem address 4) else none

/-- Read each public `cell` from the starting RV state `before` and encode its
    value as a zero-timestamp seed token. Missing (unreadable) cells make the
    construction fail. -/
def initialImageRV (before : RV.State) (cells : List Cell) :
    Option (List (MemoryToken p)) :=
  cells.mapM fun cell =>
    (cell.readRV before).map (cell.initialToken ·)

/-- Bind the initial PC of an RV state; the initial timestamp is public input. -/
def initialStateRV (before : RV.State) (timestamp : ZMod p × ZMod p) :
    PCState.State p :=
  PCState.boundary before.pc timestamp

end Airbender.Trace
